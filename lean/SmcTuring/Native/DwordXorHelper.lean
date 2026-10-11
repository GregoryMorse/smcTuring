module
public import SmcTuring.Native.StringDwordXor

public section
namespace SmcTuring.Native.DwordXorHelper
abbrev Layout := DwordLayout.Layout
@[expose] def endPC (l : Layout) := l.start+18
@[expose] def first (mode : Mode) (l : Layout) := DwordCode.Form.exchange (mode:=mode)
  (Relocation.memoryDisp mode (l.start+6) l.source)
@[expose] def middle (mode : Mode) (l : Layout) := Relocation.memoryDisp mode (l.start+12) l.destination
@[expose] def third (mode : Mode) (l : Layout) := DwordCode.Form.exchange (mode:=mode)
  (Relocation.memoryDisp mode (endPC l) l.source)
@[expose] def bytes (mode : Mode) (l : Layout) :=
  DwordCode.encode mode (first mode l) ++ DwordXor.encode (middle mode l) ++ DwordCode.encode mode (third mode l)
@[expose] def swapped (mode : Mode) (l : Layout) (state : Execution.State mode) := DwordCode.execute mode (first mode l) state
@[expose] def xored (mode : Mode) (l : Layout) (state : Execution.State mode) := DwordXor.execute mode (middle mode l) (swapped mode l state)
@[expose] def finish (mode : Mode) (l : Layout) (state : Execution.State mode) := DwordCode.execute mode (third mode l) (xored mode l state)
@[expose] def program (mode : Mode) (l : Layout) :=
  [StringDwordCopy.copy mode (first mode l),StringDwordXor.canonical mode (middle mode l),StringDwordCopy.copy mode (third mode l)]
@[expose] def stringFinish (mode : Mode) (l : Layout) (state : StringExecution.State mode) := {state with principal := finish mode l state.principal}
structure Admissible (mode : Mode) (l : Layout) : Prop where
  codeFits : endPC l < 2^(8*mode.wordBytes)
  sourceFits : l.source+4 ≤ 2^(8*mode.wordBytes)
  destinationFits : l.destination+4 ≤ 2^(8*mode.wordBytes)
  separate : l.source+4 ≤ l.destination ∨ l.destination+4 ≤ l.source
  sourceOutside : l.source+4 ≤ l.start ∨ endPC l ≤ l.source
  destinationOutside : l.destination+4 ≤ l.start ∨ endPC l ≤ l.destination
  firstRange : mode = .x64 → Relocation.SignedDelta (l.start+6) l.source
  middleRange : mode = .x64 → Relocation.SignedDelta (l.start+12) l.destination
  thirdRange : mode = .x64 → Relocation.SignedDelta (endPC l) l.source

theorem bytes_length (mode : Mode) (l : Layout) : (bytes mode l).length = 18 := by rfl

theorem exchange_effect (mode : Mode) (pc source : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 → Relocation.SignedDelta (pc+6) source)
    (fits : source < 2^(8*mode.wordBytes)) :
    DwordCode.execute mode (.exchange (Relocation.memoryDisp mode (pc+6) source)) state =
      {state with
        pc := Arithmetic.encodeNat mode (pc+6)
        accumulator := DwordCode.lift mode (DwordCode.get state.memory source)
        memory := DwordCode.put state.memory source (DwordCode.low mode state.accumulator)} := by
  have next : DwordCode.next mode (.exchange (Relocation.memoryDisp mode (pc+6) source)) state =
      Arithmetic.encodeNat mode (pc+6) := by
    rw [DwordCode.next,entry];exact BitVec.ofNat_add_ofNat pc 6
  have hit : DwordCode.address mode (.exchange (Relocation.memoryDisp mode (pc+6) source)) state = Arithmetic.encodeNat mode source := by
    change Execution.memoryAddress mode _ _ = _
    rw [next];exact Relocation.memory_hits mode _ _ range
  change { state with
    pc := DwordCode.next mode _ state
    accumulator := DwordCode.lift mode (DwordCode.get state.memory (DwordCode.address mode _ state).toNat)
    memory := DwordCode.put state.memory (DwordCode.address mode _ state).toNat (DwordCode.low mode state.accumulator)} = _
  rw [next,hit,Arithmetic.encode_nat_toNat mode source fits]

theorem first_effect (mode : Mode) (l : Layout) (valid : Admissible mode l) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode l.start) :
    swapped mode l state = {state with
      pc := Arithmetic.encodeNat mode (l.start+6)
      accumulator := DwordCode.lift mode (DwordCode.get state.memory l.source)
      memory := DwordCode.put state.memory l.source (DwordCode.low mode state.accumulator)} :=
  exchange_effect mode l.start l.source state entry valid.firstRange (by have bound := valid.sourceFits;omega)

theorem middle_effect (mode : Mode) (l : Layout) (valid : Admissible mode l) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode l.start) :
    xored mode l state = {state with
      pc := Arithmetic.encodeNat mode (l.start+12)
      accumulator := DwordCode.lift mode (DwordCode.get state.memory l.source)
      carry := false
      memory := DwordCode.put (DwordCode.put state.memory l.source (DwordCode.low mode state.accumulator)) l.destination
        (DwordCode.get state.memory l.destination ^^^ DwordCode.get state.memory l.source)} := by
  have next : (swapped mode l state).pc = Arithmetic.encodeNat mode (l.start+6) := by rw [first_effect mode l valid state entry]
  rw [xored,middle,DwordXor.located_effect mode (l.start+6) l.destination _ next
    (by simpa only [Nat.add_assoc] using valid.middleRange) (by have bound := valid.destinationFits;omega),first_effect mode l valid state entry]
  simp only [DwordCode.low_lift,Nat.add_assoc]
  rw [DwordCode.get_frame _ l.source l.destination _ (by
    intro index;have bound := index.isLt;simp only [ByteMemory.Inside];rcases valid.separate with before | after <;> omega)]


theorem third_effect (mode : Mode) (l : Layout) (valid : Admissible mode l) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (l.start+12)) :
    DwordCode.execute mode (third mode l) state = {state with
      pc := Arithmetic.encodeNat mode (endPC l)
      accumulator := DwordCode.lift mode (DwordCode.get state.memory l.source)
      memory := DwordCode.put state.memory l.source (DwordCode.low mode state.accumulator)} := by
  simpa only [third,endPC,Nat.add_assoc] using exchange_effect mode (l.start+12) l.source state entry
    (by simpa only [endPC,Nat.add_assoc] using valid.thirdRange) (by have bound := valid.sourceFits;omega)

theorem effect (mode : Mode) (l : Layout) (valid : Admissible mode l) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode l.start) :
    finish mode l state = {state with
      pc := Arithmetic.encodeNat mode (endPC l)
      accumulator := DwordCode.lift mode (DwordCode.low mode state.accumulator)
      carry := false
      memory := DwordCode.put state.memory l.destination
        (DwordCode.get state.memory l.destination ^^^ DwordCode.get state.memory l.source)} := by
  have next : (xored mode l state).pc = Arithmetic.encodeNat mode (l.start+12) := by rw [middle_effect mode l valid state entry]
  rw [finish,third_effect mode l valid _ next,middle_effect mode l valid state entry]
  rw [DwordCode.get_frame _ l.destination l.source _ (by
    intro index;have bound := index.isLt;simp only [ByteMemory.Inside];rcases valid.separate with before | after <;> omega),
    DwordCode.get_put,DwordCode.low_lift,
    DwordCode.put_commute _ l.destination l.source _ _ (by
      intro index;have bound := index.isLt;simp only [ByteMemory.Inside];rcases valid.separate with before | after <;> omega),
    DwordCode.put_overwrite,DwordCode.put_get_back]


/-- All three actual fetches follow from the initial complete helper image.
Source and destination writes are outside this helper's instruction bytes. -/
theorem trace (mode : Mode) (l : Layout) (valid : Admissible mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode l.start)
    (current : ByteMemory.bytesAt state.principal.memory l.start (bytes mode l).length = bytes mode l) :
    StringDword.Trace mode state (program mode l) (stringFinish mode l state) := by
  have firstPacket := ByteWindow.packet state.principal.memory l.start [] (DwordCode.encode mode (first mode l))
    (DwordXor.encode (middle mode l) ++ DwordCode.encode mode (third mode l)) (by simpa [bytes,List.append_assoc] using current)
  have secondPacket := ByteWindow.packet state.principal.memory l.start (DwordCode.encode mode (first mode l))
    (DwordXor.encode (middle mode l)) (DwordCode.encode mode (third mode l)) (by simpa [bytes,List.append_assoc] using current)
  have thirdPacket := ByteWindow.packet state.principal.memory l.start
    (DwordCode.encode mode (first mode l) ++ DwordXor.encode (middle mode l))
    (DwordCode.encode mode (third mode l)) [] (by simpa [bytes,List.append_assoc] using current)
  change ByteMemory.bytesAt state.principal.memory l.start 6 = DwordCode.encode mode (first mode l) at firstPacket
  change ByteMemory.bytesAt state.principal.memory (l.start+6) 6 = DwordXor.encode (middle mode l) at secondPacket
  change ByteMemory.bytesAt state.principal.memory (l.start+12) 6 = DwordCode.encode mode (third mode l) at thirdPacket
  have fits0 : l.start < 2^(8*mode.wordBytes) := by have bound := valid.codeFits;unfold endPC at bound;omega
  have fits1 : l.start+6 < 2^(8*mode.wordBytes) := by have bound := valid.codeFits;unfold endPC at bound;omega
  have fits2 : l.start+12 < 2^(8*mode.wordBytes) := by have bound := valid.codeFits;unfold endPC at bound;omega
  have firstFetch : StringDword.fetch mode state.principal.memory state.principal.pc.toNat = some (StringDwordCopy.copy mode (first mode l)) := by
    rw [entry,Arithmetic.encode_nat_toNat mode _ fits0]
    exact StringDwordCopy.copy_encoding mode _ _ _ firstPacket
  have secondCurrent : ByteMemory.bytesAt (swapped mode l state.principal).memory (l.start+6) 6 = DwordXor.encode (middle mode l) := by
    rw [first_effect mode l valid state.principal entry,DwordMixedImage.bytes_frame _ _ _ _ _ (by
      rcases valid.sourceOutside with early | late
      · left;omega
      · right;unfold endPC at late;omega)]
    exact secondPacket
  have thirdCurrent : ByteMemory.bytesAt (xored mode l state.principal).memory (l.start+12) 6 = DwordCode.encode mode (third mode l) := by
    rw [middle_effect mode l valid state.principal entry,DwordMixedImage.bytes_frame _ _ _ _ _ (by
      rcases valid.destinationOutside with early | late
      · left;omega
      · right;unfold endPC at late;omega),DwordMixedImage.bytes_frame _ _ _ _ _ (by
      rcases valid.sourceOutside with early | late
      · left;omega
      · right;unfold endPC at late;omega)]
    exact thirdPacket
  have secondFetch : StringDword.fetch mode (swapped mode l state.principal).memory (swapped mode l state.principal).pc.toNat =
      some (StringDwordXor.canonical mode (middle mode l)) := by
    have pc := congrArg Execution.State.pc (first_effect mode l valid state.principal entry)
    rw [pc,Arithmetic.encode_nat_toNat mode _ fits1]
    exact StringDwordXor.encoding mode _ _ _ secondCurrent
  have thirdFetch : StringDword.fetch mode (xored mode l state.principal).memory (xored mode l state.principal).pc.toNat =
      some (StringDwordCopy.copy mode (third mode l)) := by
    have pc := congrArg Execution.State.pc (middle_effect mode l valid state.principal entry)
    rw [pc,Arithmetic.encode_nat_toNat mode _ fits2]
    exact StringDwordCopy.copy_encoding mode _ _ _ thirdCurrent
  apply StringDword.Trace.step firstFetch
  rw [StringDwordCopy.copy_execute]
  apply StringDword.Trace.step secondFetch
  rw [StringDwordXor.execute]
  apply StringDword.Trace.step thirdFetch
  rw [StringDwordCopy.copy_execute]
  exact .nil _

theorem window (mode : Mode) (l : Layout) (valid : Admissible mode l) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode l.start) (observed count : Nat)
    (outside : l.destination+4 ≤ observed ∨ observed+count ≤ l.destination) :
    ByteMemory.bytesAt (finish mode l state).memory observed count = ByteMemory.bytesAt state.memory observed count := by
  rw [effect mode l valid state entry,DwordMixedImage.bytes_frame _ _ _ _ _ outside]

end SmcTuring.Native.DwordXorHelper

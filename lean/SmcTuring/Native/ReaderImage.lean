module
public import SmcTuring.Native.CombinedImage

public section

namespace SmcTuring.Native.ReaderImage

open Execution ControlImage

@[expose] def firstSize : Mode -> Nat | .x86 => 6 | .x64 => 7
@[expose] def secondSize : Mode -> Nat | .x86 => 5 | .x64 => 7
@[expose] def prefixSize : Mode -> Nat | .x86 => 13 | .x64 => 17
@[expose] def labelOffset : Mode -> Nat | .x86 => 14 | .x64 => 19
@[expose] def totalSize : Mode -> Nat | .x86 => 18 | .x64 => 27

@[expose] def label (mode : Mode) (start : Nat) : Word mode :=
  Arithmetic.encodeNat mode (start + labelOffset mode)

/-- The x64 reader uses fixed positive RIP offsets 12 and 5. The x86
exchange uses the computed absolute label; its store is fixed-address A3. -/
@[expose] def firstDisp (mode : Mode) (start : Nat) : BitVec 32 :=
  match mode with | .x86 => BitVec.ofNat 32 (start + 14) | .x64 => 12

@[expose] def secondDisp : Mode -> BitVec 32 | .x86 => 0 | .x64 => 5

@[expose] def packets (mode : Mode) (start : Nat) (initial : Word mode) : List (Packet mode) :=
  [.fixed (.memory .exchangeAcc (firstDisp mode start)),
    .fixed (Reader.storeForm mode (label mode start) (secondDisp mode)),
    .fixed .exchangeIndirect, .owned initial]

@[expose] def firstEntry (mode : Mode) (start : Nat) : Entry mode :=
  { pc := start, packet := .fixed (.memory .exchangeAcc (firstDisp mode start)) }

@[expose] def secondEntry (mode : Mode) (start : Nat) : Entry mode :=
  { pc := start + firstSize mode, packet := .fixed (Reader.storeForm mode (label mode start) (secondDisp mode)) }

@[expose] def thirdEntry (mode : Mode) (start : Nat) : Entry mode :=
  { pc := start + firstSize mode + secondSize mode, packet := .fixed .exchangeIndirect }

@[expose] def lastEntry (mode : Mode) (start : Nat) (initial : Word mode) : Entry mode :=
  { pc := start + prefixSize mode, packet := .owned initial }

theorem packet_size (mode : Mode) (start : Nat) (initial : Word mode) :
    ControlPacking.size mode (packets mode start initial) = totalSize mode := by
  cases mode <;> rfl

theorem placed_roles (mode : Mode) (start : Nat) (initial : Word mode) :
    ControlPacking.place mode start (packets mode start initial) =
      [firstEntry mode start, secondEntry mode start, thirdEntry mode start, lastEntry mode start initial] := by
  cases mode <;> simp [ControlPacking.place, packets, Packet.bytes, encode, Reader.storeForm,
    wordPrefix, MemoryOp.prefix, MemoryOp.trailer, Mode.wordBytes, LittleEndian.wordEncode, firstEntry, secondEntry, thirdEntry,
    lastEntry, firstSize, secondSize, prefixSize, Nat.add_assoc]

theorem label_location (mode : Mode) (start : Nat) (initial : Word mode)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes)) :
    (label mode start).toNat = (lastEntry mode start initial).pc + moffsOperandOffset mode := by
  have small : start + labelOffset mode < 2 ^ (8 * mode.wordBytes) := by
    cases mode <;> simp [totalSize, labelOffset, Mode.wordBytes] at * <;> omega
  rw [label, Arithmetic.encode_nat_toNat mode _ small]
  cases mode <;> simp [lastEntry, labelOffset, prefixSize, moffsOperandOffset, wordPrefix, Nat.add_assoc]

theorem label_owned (mode : Mode) (start : Nat) (initial : Word mode)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes)) :
    Owned mode (ControlPacking.place mode start (packets mode start initial)) (label mode start) := by
  refine ⟨lastEntry mode start initial, ?_, ⟨initial, rfl⟩, label_location mode start initial fits⟩
  rw [placed_roles]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem swapped_pc (mode : Mode) (start : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    (Reader.swapped mode state (firstDisp mode start)).pc = Arithmetic.encodeNat mode (start + firstSize mode) := by
  have length : instructionLength mode (.memory .exchangeAcc (firstDisp mode start)) = firstSize mode := by
    cases mode <;> rfl
  change state.pc + Arithmetic.encodeNat mode (instructionLength mode (.memory .exchangeAcc (firstDisp mode start))) = _
  rw [location, length]
  exact BitVec.ofNat_add_ofNat start (firstSize mode)

theorem restored_pc (mode : Mode) (start : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    (Reader.restored mode state (label mode start) (firstDisp mode start) (secondDisp mode)).pc =
      Arithmetic.encodeNat mode (start + firstSize mode + secondSize mode) := by
  have next : (Reader.restored mode state (label mode start) (firstDisp mode start) (secondDisp mode)).pc =
      (Reader.swapped mode state (firstDisp mode start)).pc + Arithmetic.encodeNat mode (secondSize mode) := by
    cases mode <;> rfl
  rw [next, swapped_pc mode start state location]
  exact BitVec.ofNat_add_ofNat (start + firstSize mode) (secondSize mode)

theorem dereferenced_pc (mode : Mode) (start : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    (Reader.dereferenced mode state (label mode start) (firstDisp mode start) (secondDisp mode)).pc =
      Arithmetic.encodeNat mode (start + prefixSize mode) := by
  change (Reader.restored mode state (label mode start) (firstDisp mode start) (secondDisp mode)).pc +
    Arithmetic.encodeNat mode (instructionLength mode .exchangeIndirect) = _
  rw [restored_pc mode start state location]
  unfold Arithmetic.encodeNat
  rw [BitVec.ofNat_add_ofNat]
  congr 1
  cases mode <;> simp [instructionLength, wordPrefix, firstSize, secondSize, prefixSize, Nat.add_assoc]

theorem finish_pc (mode : Mode) (start : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    (Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)).pc =
      Arithmetic.encodeNat mode (start + totalSize mode) := by
  change (Reader.dereferenced mode state (label mode start) (firstDisp mode start) (secondDisp mode)).pc +
    Arithmetic.encodeNat mode (instructionLength mode (.moffs (load mode state.memory (label mode start)))) = _
  rw [dereferenced_pc mode start state location]
  unfold Arithmetic.encodeNat
  rw [BitVec.ofNat_add_ofNat]
  congr 1
  cases mode <;> simp [instructionLength, wordPrefix, prefixSize, totalSize, Mode.wordBytes, Nat.add_assoc]

theorem finish_position (mode : Mode) (start : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes)) :
    (Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)).pc.toNat =
      start + totalSize mode := by
  rw [finish_pc mode start state location, Arithmetic.encode_nat_toNat mode _ fits]

theorem first_hits (mode : Mode) (start : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    memoryAddress mode (nextPC mode (.memory .exchangeAcc (firstDisp mode start)) state)
      (firstDisp mode start) = label mode start := by
  cases mode with
  | x86 => rfl
  | x64 =>
    have extended : (12 : BitVec 32).signExtend 64 = (12 : BitVec 64) := by decide
    change BitVec.add (BitVec.add state.pc (Arithmetic.encodeNat .x64 7)) ((12 : BitVec 32).signExtend 64) = _
    rw [location, extended]
    change BitVec.ofNat 64 start + BitVec.ofNat 64 7 + BitVec.ofNat 64 12 = BitVec.ofNat 64 (start + 19)
    simp [BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem second_hits (mode : Mode) (start : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    Reader.storeAddress mode (Reader.swapped mode state (firstDisp mode start))
      (label mode start) (secondDisp mode) = label mode start := by
  cases mode with
  | x86 => rfl
  | x64 =>
    have extended : (5 : BitVec 32).signExtend 64 = (5 : BitVec 64) := by decide
    change BitVec.add (BitVec.add (Reader.swapped .x64 state (firstDisp .x64 start)).pc
      (Arithmetic.encodeNat .x64 7)) ((5 : BitVec 32).signExtend 64) = _
    rw [swapped_pc .x64 start state location, extended]
    change BitVec.ofNat 64 (start + 7) + BitVec.ofNat 64 7 + BitVec.ofNat 64 5 = BitVec.ofNat 64 (start + 19)
    simp [BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem reached_positions (mode : Mode) (start : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes)) :
    And (state.pc.toNat = start)
      (And ((Reader.swapped mode state (firstDisp mode start)).pc.toNat = (secondEntry mode start).pc)
        (And ((Reader.restored mode state (label mode start) (firstDisp mode start) (secondDisp mode)).pc.toNat =
          (thirdEntry mode start).pc)
          ((Reader.dereferenced mode state (label mode start) (firstDisp mode start) (secondDisp mode)).pc.toNat =
            start + prefixSize mode))) := by
  have startFits : start < 2 ^ (8 * mode.wordBytes) := by omega
  have firstFits : start + firstSize mode < 2 ^ (8 * mode.wordBytes) := by
    cases mode <;> simp [firstSize, totalSize, Mode.wordBytes] at * <;> omega
  have secondFits : start + firstSize mode + secondSize mode < 2 ^ (8 * mode.wordBytes) := by
    cases mode <;> simp [firstSize, secondSize, totalSize, Mode.wordBytes] at * <;> omega
  have thirdFits : start + prefixSize mode < 2 ^ (8 * mode.wordBytes) := by
    cases mode <;> simp [prefixSize, totalSize, Mode.wordBytes] at * <;> omega
  rw [location, swapped_pc mode start state location, restored_pc mode start state location,
    dereferenced_pc mode start state location]
  exact ⟨Arithmetic.encode_nat_toNat mode start startFits,
    Arithmetic.encode_nat_toNat mode _ firstFits, Arithmetic.encode_nat_toNat mode _ secondFits,
    Arithmetic.encode_nat_toNat mode _ thirdFits⟩

/-- All four fetches are consequences of constructed placement and the code
invariant. No fetch premise or manually supplied packet length is required. -/
theorem trace (mode : Mode) (start gridBase : Nat) (initial : Word mode) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + totalSize mode <= gridBase - moffsOperandOffset mode)
    (intact : CombinedImage.Intact mode (packets mode start initial) start gridBase state.memory)
    (pointerOwned : Protected.GridOwned mode gridBase (load mode state.memory (label mode start))) :
    Fetch.Trace mode state
      [.memory .exchangeAcc (firstDisp mode start), Reader.storeForm mode (label mode start) (secondDisp mode),
        .exchangeIndirect, .moffs (load mode state.memory (label mode start))]
      (Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)) := by
  have firstMember : List.Mem (firstEntry mode start) (ControlPacking.place mode start (packets mode start initial)) := by
    rw [placed_roles]; exact List.Mem.head _
  have secondMember : List.Mem (secondEntry mode start) (ControlPacking.place mode start (packets mode start initial)) := by
    rw [placed_roles]; exact List.Mem.tail _ (List.Mem.head _)
  have thirdMember : List.Mem (thirdEntry mode start) (ControlPacking.place mode start (packets mode start initial)) := by
    rw [placed_roles]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have lastMember : List.Mem (lastEntry mode start initial) (ControlPacking.place mode start (packets mode start initial)) := by
    rw [placed_roles]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have positions := reached_positions mode start state location fits
  have firstHits := first_hits mode start state location
  have secondHits := second_hits mode start state location
  have realGap : start + ControlPacking.size mode (packets mode start initial) <= gridBase - moffsOperandOffset mode := by
    rw [packet_size]; exact gap
  have labelOwned : CombinedImage.Owned mode (packets mode start initial) start gridBase (label mode start) :=
    Or.inl (label_owned mode start initial fits)
  have swappedIntact : CombinedImage.Intact mode (packets mode start initial) start gridBase
      (Reader.swapped mode state (firstDisp mode start)).memory := by
    apply CombinedImage.execute_intact mode _ start gridBase state (.memory .exchangeAcc (firstDisp mode start)) enough realGap intact
    change CombinedImage.Owned mode _ start gridBase
      (memoryAddress mode (nextPC mode (.memory .exchangeAcc (firstDisp mode start)) state) (firstDisp mode start))
    rw [firstHits]; exact labelOwned
  have current := Protected.current_moffs mode state.memory (start + prefixSize mode) (intact.1 _ lastMember)
  have word : Protected.wordAt mode state.memory (start + prefixSize mode + moffsOperandOffset mode) =
      load mode state.memory (label mode start) := by
    unfold load Protected.wordAt
    rw [label_location mode start initial fits]
    rfl
  rw [word] at current
  have pointerExternal : External mode (ControlPacking.place mode start (packets mode start initial))
      (load mode state.memory (label mode start)) := by
    apply ControlPacking.above_external
    cases pointerOwned with
    | intro cell address =>
      rw [address]
      unfold Layout.fieldAddress
      omega
  apply Reader.trace_of_fetches
  · rw [positions.1]
    exact fetch_current mode (firstEntry mode start) state.memory (intact.1 _ firstMember)
  · rw [positions.2.1]
    exact fetch_current mode (secondEntry mode start) _ (swappedIntact.1 _ secondMember)
  · rw [Reader.restored_memory mode state _ _ _ firstHits secondHits, positions.2.2.1]
    exact fetch_current mode (thirdEntry mode start) state.memory (intact.1 _ thirdMember)
  · apply Reader.fetch_last mode state _ _ _ firstHits secondHits
    · rw [positions.2.2.2]; exact current
    · apply Or.inr
      intro index
      let observed : Fin ((lastEntry mode start initial).bytes mode).length :=
        ⟨index.val, by simpa [lastEntry, Entry.bytes, Packet.bytes, instructionLength] using index.isLt⟩
      simpa only [positions.2.2.2, lastEntry] using pointerExternal (lastEntry mode start initial) lastMember observed

theorem owned_run (mode : Mode) (start gridBase : Nat) (initial : Word mode) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (pointerOwned : Protected.GridOwned mode gridBase (load mode state.memory (label mode start))) :
    Writes.OwnedRun mode (CombinedImage.Owned mode (packets mode start initial) start gridBase)
      [.memory .exchangeAcc (firstDisp mode start), Reader.storeForm mode (label mode start) (secondDisp mode),
        .exchangeIndirect, .moffs (load mode state.memory (label mode start))] state := by
  have fields := Reader.four_writes_owned mode state (label mode start) (firstDisp mode start) (secondDisp mode)
    (first_hits mode start state location) (second_hits mode start state location)
    (CombinedImage.Owned mode (packets mode start initial) start gridBase)
    (Or.inl (label_owned mode start initial fits)) (Or.inr pointerOwned)
  simpa only [Writes.OwnedRun, and_true, Reader.swapped, Reader.restored, Reader.dereferenced] using fields

theorem result (mode : Mode) (start gridBase : Nat) (initial : Word mode) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + totalSize mode <= gridBase - moffsOperandOffset mode)
    (intact : CombinedImage.Intact mode (packets mode start initial) start gridBase state.memory)
    (pointerOwned : Protected.GridOwned mode gridBase (load mode state.memory (label mode start))) :
    And ((Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)).memory = state.memory)
      (And ((Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)).accumulator =
        load mode state.memory (load mode state.memory (label mode start)))
        (And ((Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)).stack = state.stack)
          ((Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)).carry = state.carry))) :=
  Reader.trace_result mode state _ _ _ _ (first_hits mode start state location) (second_hits mode start state location)
    (trace mode start gridBase initial state location fits enough gap intact pointerOwned)

theorem initially_intact (mode : Mode) (start gridBase : Nat) (initial : Word mode) (values : Nat -> Word mode)
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + totalSize mode <= gridBase - moffsOperandOffset mode) :
    CombinedImage.Intact mode (packets mode start initial) start gridBase
      (CombinedImage.image mode (packets mode start initial) start gridBase values) := by
  apply CombinedImage.initially_intact mode _ start gridBase values enough
  rw [packet_size]; exact gap

theorem initial_pointer (mode : Mode) (start gridBase : Nat) (initial : Word mode) (values : Nat -> Word mode)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + totalSize mode <= gridBase - moffsOperandOffset mode) :
    load mode (CombinedImage.image mode (packets mode start initial) start gridBase values) (label mode start) = initial := by
  have member : List.Mem (lastEntry mode start initial) (ControlPacking.place mode start (packets mode start initial)) := by
    rw [placed_roles]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have bytes := ControlPacking.initial_packet mode (packets mode start initial) start
    (GridImage.image mode gridBase values) (lastEntry mode start initial) member
  have encoded := Fetch.fetch_current_encoding mode
    (CombinedImage.image mode (packets mode start initial) start gridBase values)
    (lastEntry mode start initial).pc (.moffs initial) bytes
  have live := Protected.fetch_moffs mode
    (CombinedImage.image mode (packets mode start initial) start gridBase values)
    (lastEntry mode start initial).pc
    ((initially_intact mode start gridBase initial values enough gap).1 _ member)
  rw [<-label_location mode start initial fits] at live
  exact Form.moffs.inj (Option.some.inj (live.symm.trans encoded))

/-- The initialized reader executes from its constructed bytes with its exact
initial pointer. Its only address hypotheses are capacity and grid ownership. -/
theorem initialized_trace (mode : Mode) (start gridBase : Nat) (initial : Word mode) (values : Nat -> Word mode)
    (state : State mode) (location : state.pc = Arithmetic.encodeNat mode start)
    (memory : state.memory = CombinedImage.image mode (packets mode start initial) start gridBase values)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + totalSize mode <= gridBase - moffsOperandOffset mode)
    (pointerOwned : Protected.GridOwned mode gridBase initial) :
    Fetch.Trace mode state
      [.memory .exchangeAcc (firstDisp mode start), Reader.storeForm mode (label mode start) (secondDisp mode),
        .exchangeIndirect, .moffs (load mode state.memory (label mode start))]
      (Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)) := by
  apply trace mode start gridBase initial state location fits enough gap
  · rw [memory]; exact initially_intact mode start gridBase initial values enough gap
  · rw [memory, initial_pointer mode start gridBase initial values fits enough gap]; exact pointerOwned

theorem initialized_accumulator (mode : Mode) (start gridBase cell : Nat) (initial : Word mode) (values : Nat -> Word mode)
    (state : State mode) (location : state.pc = Arithmetic.encodeNat mode start)
    (memory : state.memory = CombinedImage.image mode (packets mode start initial) start gridBase values)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + totalSize mode <= gridBase - moffsOperandOffset mode)
    (pointer : initial.toNat = Layout.fieldAddress mode gridBase cell) :
    (Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)).accumulator = values cell := by
  rw [Reader.finish_accumulator mode state _ _ _ (first_hits mode start state location) (second_hits mode start state location),
    memory, initial_pointer mode start gridBase initial values fits enough gap]
  unfold load
  rw [pointer]
  apply CombinedImage.initial_word mode _ start gridBase cell values enough
  rw [packet_size]; exact gap

end SmcTuring.Native.ReaderImage

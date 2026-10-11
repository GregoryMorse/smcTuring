module
public import SmcTuring.Native.DwordXorSequence
public import SmcTuring.Native.StringCopyWrites

public section
namespace SmcTuring.Native.DwordXorWrites

theorem address (mode : Mode) (d : BitVec 32) (state : StringExecution.State mode) :
    (StringWrites.packet mode (StringStoreWrites.liftDword mode (StringDwordXor.canonical mode d)) state).address=
      (DwordXor.address mode d state.principal).toNat := by cases mode <;> rfl

theorem length (mode : Mode) (d : BitVec 32) (state : StringExecution.State mode) :
    (StringWrites.packet mode (StringStoreWrites.liftDword mode (StringDwordXor.canonical mode d)) state).bytes.length=4 := by
  cases mode <;> exact LittleEndian.word_encode_length _ _

theorem xor_write (mode : Mode) (codeStart codeEnd pc target : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+6) target)
    (fits : target<2^(8*mode.wordBytes)) (inside : codeStart≤target ∧ target+4≤codeEnd) :
    StringWrites.CodeWrite mode codeStart codeEnd
      (StringStoreWrites.liftDword mode (StringDwordXor.canonical mode (Relocation.memoryDisp mode (pc+6) target))) state := by
  have next : DwordXor.next mode state.principal=Arithmetic.encodeNat mode (pc+6) := by
    rw [DwordXor.next,entry];exact BitVec.ofNat_add_ofNat pc 6
  have hit : DwordXor.address mode (Relocation.memoryDisp mode (pc+6) target) state.principal=Arithmetic.encodeNat mode target := by
    rw [DwordXor.address,next];exact Relocation.memory_hits mode _ _ range
  unfold StringWrites.CodeWrite
  rw [address,length,hit,Arithmetic.encode_nat_toNat mode _ fits]
  exact ⟨by decide,inside⟩

theorem exchange_write (mode : Mode) (codeStart codeEnd pc target : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+6) target)
    (fits : target<2^(8*mode.wordBytes)) (inside : codeStart≤target ∧ target+4≤codeEnd) :
    StringWrites.CodeWrite mode codeStart codeEnd
      (StringStoreWrites.liftDword mode (StringDwordCopy.copy mode (.exchange (Relocation.memoryDisp mode (pc+6) target)))) state := by
  have next : DwordCode.next mode (.exchange (Relocation.memoryDisp mode (pc+6) target)) state.principal=Arithmetic.encodeNat mode (pc+6) := by
    rw [DwordCode.next,entry];exact BitVec.ofNat_add_ofNat pc 6
  have hit : DwordCode.address mode (.exchange (Relocation.memoryDisp mode (pc+6) target)) state.principal=Arithmetic.encodeNat mode target := by
    change Execution.memoryAddress mode _ _=_
    rw [next];exact Relocation.memory_hits mode _ _ range
  apply StringCopyWrites.copy_write mode codeStart codeEnd _ state
  rw [hit,Arithmetic.encode_nat_toNat mode _ fits]
  exact inside

theorem helper_run (mode : Mode) (layout : DwordXorHelper.Layout) (state : StringExecution.State mode) :
    StringWrites.run mode ((DwordXorHelper.program mode layout).map (StringStoreWrites.liftDword mode)) state=
      DwordXorHelper.stringFinish mode layout state := by
  change StringDword.execute mode (StringDwordCopy.copy mode (DwordXorHelper.third mode layout))
    (StringDword.execute mode (StringDwordXor.canonical mode (DwordXorHelper.middle mode layout))
      (StringDword.execute mode (StringDwordCopy.copy mode (DwordXorHelper.first mode layout)) state))=_
  rw [StringDwordCopy.copy_execute,StringDwordXor.execute,StringDwordCopy.copy_execute]
  rfl

theorem helper_owned (mode : Mode) (codeStart codeEnd : Nat) (layout : DwordXorHelper.Layout) (valid : DwordXorHelper.Admissible mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (sourceInside : codeStart≤layout.source ∧ layout.source+4≤codeEnd)
    (destinationInside : codeStart≤layout.destination ∧ layout.destination+4≤codeEnd) :
    StringWrites.OwnedRun mode codeStart codeEnd ((DwordXorHelper.program mode layout).map (StringStoreWrites.liftDword mode)) state := by
  have sourceFits : layout.source<2^(8*mode.wordBytes) := by have bound:=valid.sourceFits;omega
  have targetFits : layout.destination<2^(8*mode.wordBytes) := by have bound:=valid.destinationFits;omega
  have first:=exchange_write mode codeStart codeEnd layout.start layout.source state entry valid.firstRange sourceFits sourceInside
  let swapped : StringExecution.State mode := {state with principal:=DwordXorHelper.swapped mode layout state.principal}
  let xored : StringExecution.State mode := {state with principal:=DwordXorHelper.xored mode layout state.principal}
  have secondPC : swapped.principal.pc=Arithmetic.encodeNat mode (layout.start+6) := by
    dsimp only [swapped]
    rw [DwordXorHelper.first_effect mode layout valid state.principal entry]
  have second:=xor_write mode codeStart codeEnd (layout.start+6) layout.destination swapped secondPC
    (by simpa only [Nat.add_assoc] using valid.middleRange) targetFits destinationInside
  have thirdPC : xored.principal.pc=Arithmetic.encodeNat mode (layout.start+12) := by
    dsimp only [xored]
    rw [DwordXorHelper.middle_effect mode layout valid state.principal entry]
  have third:=exchange_write mode codeStart codeEnd (layout.start+12) layout.source xored thirdPC
    (by simpa only [DwordXorHelper.endPC,Nat.add_assoc] using valid.thirdRange) sourceFits sourceInside
  constructor
  · exact first
  · change StringWrites.OwnedRun mode codeStart codeEnd _
      (StringDword.execute mode (StringDwordCopy.copy mode (DwordXorHelper.first mode layout)) state)
    rw [StringDwordCopy.copy_execute]
    constructor
    · simpa only [swapped,DwordXorHelper.swapped,DwordXorHelper.middle,Nat.add_assoc,Nat.reduceAdd] using second
    · change StringWrites.OwnedRun mode codeStart codeEnd _
        (StringDword.execute mode (StringDwordXor.canonical mode (DwordXorHelper.middle mode layout)) swapped)
      rw [StringDwordXor.execute]
      exact ⟨by simpa only [xored,swapped,DwordXorHelper.xored,DwordXorHelper.swapped,DwordXorHelper.third,
        DwordXorHelper.endPC,Nat.add_assoc,Nat.reduceAdd] using third,trivial⟩

theorem sequence_run (mode : Mode) (layouts : List DwordXorHelper.Layout) (state : StringExecution.State mode) :
    StringWrites.run mode ((DwordXorSequence.program mode layouts).map (StringStoreWrites.liftDword mode)) state=
      DwordXorSequence.finish mode layouts state := by
  induction layouts generalizing state with
  | nil => rfl
  | cons layout layouts ih =>
    rw [DwordXorSequence.program,List.flatMap_cons,List.map_append,StringWrites.run_append,helper_run]
    exact ih _

theorem sequence_owned (mode : Mode) (codeStart codeEnd : Nat) (layouts : List DwordXorHelper.Layout) (start : Nat)
    (chain : DwordXorSequence.Contiguous start layouts) (valid : ∀ layout∈layouts,DwordXorHelper.Admissible mode layout)
    (fields : ∀ layout∈layouts,(codeStart≤layout.source ∧ layout.source+4≤codeEnd) ∧
      (codeStart≤layout.destination ∧ layout.destination+4≤codeEnd))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringWrites.OwnedRun mode codeStart codeEnd ((DwordXorSequence.program mode layouts).map (StringStoreWrites.liftDword mode)) state := by
  induction layouts generalizing start state with
  | nil => trivial
  | cons layout layouts ih =>
    have ready:=valid layout (List.Mem.head _)
    have spans:=fields layout (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode layout.start := by rw [chain.1];exact entry
    have first:=helper_owned mode codeStart codeEnd layout ready state location spans.1 spans.2
    have next : (DwordXorHelper.stringFinish mode layout state).principal.pc=Arithmetic.encodeNat mode (DwordXorHelper.endPC layout) := by
      change (DwordXorHelper.finish mode layout state.principal).pc=_
      rw [DwordXorHelper.effect mode layout ready state.principal location]
    have rest:=ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
      (fun later member => fields later (List.Mem.tail _ member)) _ next
    rw [DwordXorSequence.program,List.flatMap_cons,List.map_append,StringWrites.owned_run_append,helper_run]
    exact ⟨first,rest⟩

end SmcTuring.Native.DwordXorWrites

module
public import SmcTuring.Native.MixedWriteRuns
public import SmcTuring.Native.DwordMixedSequence

public section
namespace SmcTuring.Native.DwordMixedWrites

theorem copy_run (mode : Mode) (layout : DwordLayout.Layout) (state : Execution.State mode) :
    MixedWriteRuns.run mode ((DwordLayout.program mode layout).map MixedDword.Form.copy) state=DwordEffects.finish mode layout state := by
  rfl

theorem copy_owned (mode : Mode) (codeStart codeEnd : Nat) (layout : DwordLayout.Layout) (valid : DwordLayout.Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode layout.start)
    (sourceInside : codeStart≤layout.source ∧ layout.source+4≤codeEnd)
    (destinationInside : codeStart≤layout.destination ∧ layout.destination+4≤codeEnd) :
    MixedDword.OwnedRun mode (fun address width => codeStart≤address ∧ address+width≤codeEnd)
      ((DwordLayout.program mode layout).map MixedDword.Form.copy) state :=
  MixedWriteRuns.copy_owned mode codeStart codeEnd _ state (DwordImage.supported_run mode layout valid state entry _ sourceInside destinationInside)

/-- Every mask/copy helper has actual future PCs derived from its preceding
three stores, with complete original static source/destination spans. -/
theorem sequence_owned (mode : Mode) (codeStart codeEnd : Nat) (layouts : List DwordLayout.Layout) (start : Nat)
    (chain : DwordMixedSequence.Contiguous mode start layouts) (valid : ∀ layout∈layouts,DwordLayout.Admissible mode layout)
    (fields : ∀ layout∈layouts,(codeStart≤layout.source ∧ layout.source+4≤codeEnd) ∧
      (codeStart≤layout.destination ∧ layout.destination+4≤codeEnd))
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode start) :
    MixedDword.OwnedRun mode (fun address width => codeStart≤address ∧ address+width≤codeEnd) (DwordMixedSequence.program mode layouts) state := by
  induction layouts generalizing start state with
  | nil => trivial
  | cons layout layouts ih =>
    have v:=valid layout (List.Mem.head _)
    have f:=fields layout (List.Mem.head _)
    have location : state.pc=Arithmetic.encodeNat mode layout.start := by rw [chain.1];exact entry
    have first:=copy_owned mode codeStart codeEnd layout v state location f.1 f.2
    have next : (DwordEffects.finish mode layout state).pc=Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      rw [DwordEffects.effect mode layout v state location]
    have rest:=ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
      (fun later member => fields later (List.Mem.tail _ member)) _ next
    rw [DwordMixedSequence.program,List.flatMap_cons,MixedWriteRuns.owned_run_append,copy_run]
    exact ⟨first,rest⟩

end SmcTuring.Native.DwordMixedWrites

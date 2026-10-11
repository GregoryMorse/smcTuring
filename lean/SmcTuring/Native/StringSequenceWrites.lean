module
public import SmcTuring.Native.StringCopyWrites
public import SmcTuring.Native.StringDwordSequence

public section
namespace SmcTuring.Native.StringSequenceWrites

theorem word_run (mode : Mode) (layout : ConversionLayout.Layout) (state : StringExecution.State mode) :
    StringWrites.run mode ((StringDwordCopy.wordProgram mode layout).map (StringStoreWrites.liftDword mode)) state=
      StringDwordCopy.wordFinish mode layout state := by
  simp only [StringDwordCopy.wordProgram,ConversionLayout.program,List.map_cons,List.map_nil,StringWrites.run,
    StringStoreWrites.liftDword,StringStack.execute,StringControl.execute]
  rw [StringDwordCopy.native_execute,StringDwordCopy.native_execute,StringDwordCopy.native_execute]
  rfl

theorem dword_run (mode : Mode) (layout : DwordLayout.Layout) (state : StringExecution.State mode) :
    StringWrites.run mode ((StringDwordCopy.dwordProgram mode layout).map (StringStoreWrites.liftDword mode)) state=
      StringDwordCopy.dwordFinish mode layout state := by
  simp only [StringDwordCopy.dwordProgram,DwordLayout.program,List.map_cons,List.map_nil,StringWrites.run,
    StringStoreWrites.liftDword,StringStack.execute,StringControl.execute]
  rw [StringDwordCopy.copy_execute,StringDwordCopy.copy_execute,StringDwordCopy.copy_execute]
  rfl

/-- Every helper's entry PC follows from the preceding actual three stores.
Only original static code-word spans and relocation bounds are premises. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (layouts : List DwordLayout.Layout) (start : Nat)
    (chain : StringDwordSequence.Contiguous mode start layouts)
    (valid : ∀ layout∈layouts,DwordLayout.Admissible mode layout)
    (fields : ∀ layout∈layouts,(codeStart≤layout.source ∧ layout.source+4≤codeEnd) ∧
      (codeStart≤layout.destination ∧ layout.destination+4≤codeEnd))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringDwordSequence.program mode layouts).map (StringStoreWrites.liftDword mode)) state := by
  induction layouts generalizing start state with
  | nil => trivial
  | cons layout layouts ih =>
    have v:=valid layout (List.Mem.head _)
    have f:=fields layout (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode layout.start := by rw [chain.1];exact entry
    have first:=StringCopyWrites.dword mode codeStart codeEnd layout v state location f.1 f.2
    have next : (StringDwordCopy.dwordFinish mode layout state).principal.pc=Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      change (DwordEffects.finish mode layout state.principal).pc=_
      rw [DwordEffects.effect mode layout v state.principal location]
    have rest:=ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
      (fun later member => fields later (List.Mem.tail _ member)) _ next
    rw [StringDwordSequence.program,List.flatMap_cons,List.map_append,StringWrites.owned_run_append,dword_run]
    exact ⟨first,rest⟩

end SmcTuring.Native.StringSequenceWrites

module
public import SmcTuring.Appendix.Listing8DirectionTrace
public import SmcTuring.Native.DwordPacketWrites
public import SmcTuring.Native.StringSequenceWrites

public section
namespace SmcTuring.Appendix.Listing8DirectionWrites
open Native Listing8DirectionLayout

theorem helper_fields (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout)
    (inside : codeStart≤layout.start ∧ endPC mode layout≤codeEnd) :
    ∀ helper∈helpers mode layout,(codeStart≤helper.source ∧ helper.source+4≤codeEnd) ∧
      (codeStart≤helper.destination ∧ helper.destination+4≤codeEnd) := by
  intro helper member
  cases mode
  all_goals simp only [helpers,duplicate,copy,List.nil_append,List.cons_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at inside ⊢;omega

theorem arithmetic_fields (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout)
    (inside : codeStart≤layout.start ∧ endPC mode layout≤codeEnd) :
    ∀ site∈arithmetic mode layout,codeStart≤site.target ∧ site.target+4≤codeEnd := by
  intro site member
  cases mode
  all_goals simp only [arithmetic,group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at inside ⊢;omega

theorem helper_run (mode : Mode) (layout : Layout) (state : StringExecution.State mode) :
    StringWrites.run mode ((StringDwordSequence.program mode (helpers mode layout)).map (StringStoreWrites.liftDword mode)) state=
      Listing8DirectionTrace.helperFinish mode layout state := by
  unfold Listing8DirectionTrace.helperFinish StringDwordSequence.program StringDwordSequence.finish
  generalize helpers mode layout=layouts
  induction layouts generalizing state with
  | nil => rfl
  | cons helper helpers ih =>
    rw [List.flatMap_cons,List.map_append,StringWrites.run_append,StringSequenceWrites.dword_run]
    exact ih (StringDwordCopy.dwordFinish mode helper state)

/-- Actual helper copies and live AND/NOT/AND/OR packets own all selected
fields. Their changing immediate values and future PCs are computed. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout)
    (inside : codeStart≤layout.start ∧ endPC mode layout≤codeEnd) (capacity : endPC mode layout<2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start) :
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8DirectionTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
  have first:=StringSequenceWrites.owned mode codeStart codeEnd (helpers mode layout) layout.start (helper_chain mode layout)
    (Listing8DirectionBounds.helper_valid mode layout capacity) (helper_fields mode codeStart codeEnd layout inside) state entry
  have last:=DwordPacketWrites.owned mode codeStart codeEnd (arithmetic mode layout) (backPC mode layout) (arithmetic_chain mode layout)
    (Listing8DirectionBounds.arithmetic_valid mode layout capacity) (arithmetic_fields mode codeStart codeEnd layout inside)
    (Listing8DirectionTrace.helperFinish mode layout state) (Listing8DirectionTrace.helper_endpoint mode layout capacity state entry)
  rw [Listing8DirectionTrace.program,List.map_append,StringWrites.owned_run_append,helper_run]
  exact ⟨first,last⟩

end SmcTuring.Appendix.Listing8DirectionWrites

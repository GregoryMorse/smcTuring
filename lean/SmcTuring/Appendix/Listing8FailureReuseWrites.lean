module
public import SmcTuring.Appendix.Listing8FailureWrites
public import SmcTuring.Appendix.Listing8FailureReuseEffects

public section
namespace SmcTuring.Appendix.Listing8FailureReuseWrites
open Native Listing8FailureLayout Listing8FailureBounds Listing8FailureImage Listing8FailureWrites
abbrev Placement := Listing8FailureWrites.Placement

set_option maxHeartbeats 1000000 in
/-- The actual reset, DEFDATA, seven full-width comparison operations and
four live fail-mask/CALL-operand packets all store complete fields in code. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (bounds : Bounds mode layout)
    (placed : Placement mode codeStart codeEnd layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start) (current : Listing8FailureReuseImage.Current mode layout state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8FailureTrace.program mode layout state).map StringStack.Form.previous) state := by
  have ⟨sourceInside,maskInside⟩:=fields mode codeStart codeEnd layout placed
  have cap:=bounds.capacity
  have coords:=positions mode layout
  have maskFits : mask mode layout<2^(8*mode.wordBytes) := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have firstField:=MixedLocatedWrites.field mode codeStart codeEnd layout.start (mask mode layout) (.store 0 0) state.principal rfl entry
    (by cases mode <;> simp [DwordArithmetic.length,Relocation.SignedDelta,Relocation.delta] at coords ⊢ <;> omega) maskFits maskInside
  have first:=StringMixedWrites.code_write mode codeStart codeEnd (.arithmetic (reset mode layout)) state firstField
  have second:=StringInitWrites.owned mode codeStart codeEnd (ownerPC layout) layout.sentinel (resetState mode layout state)
    (reset_pc mode layout bounds state entry) (owner_fits mode layout bounds) bounds.sentinelFits sourceInside placed.sentinel
    (Listing8FailureReuseImage.reset_owner mode layout bounds state entry current)
  have third:=ControlPacketWrites.owned mode codeStart codeEnd (Listing8FailComparison.sites mode (comparison mode layout))
    (comparison mode layout).start (Listing8FailComparison.chain mode (comparison mode layout))
    (Listing8FailComparison.valid mode (comparison mode layout) (comparison_bounds mode layout bounds))
    (comparison_fields mode codeStart codeEnd layout placed) (ownerFinish mode layout state)
    (Listing8FailureReuseImage.comparison_entry mode layout bounds state entry current)
  have last:=DwordPacketWrites.owned mode codeStart codeEnd (post mode layout) (notPC mode layout) (post_chain mode layout)
    (post_valid mode layout bounds) (post_fields mode codeStart codeEnd layout placed) (comparisonFinish mode layout state)
    (Listing8FailureReuseEffects.comparison_endpoint mode layout bounds state entry current)
  have firstRun : StringWrites.run mode [StringStack.Form.previous (.previous (StringDwordArithmetic.canonical mode (reset mode layout)))] state=
      resetState mode layout state := by
    change StringDword.execute mode (StringDwordArithmetic.canonical mode (reset mode layout)) state=_
    rw [StringDwordArithmetic.execute];rfl
  have lifting : (fun form : StringForm.Form mode => StringStack.Form.previous (StringControl.Form.previous (StringDword.Form.string form)))=
      StringWrites.liftString mode := by funext form;rfl
  have secondRun : StringWrites.run mode ((Listing8FailureTrace.ownerProgram mode layout).map StringStack.Form.previous)
      (resetState mode layout state)=ownerFinish mode layout state := by
    simpa only [Listing8FailureTrace.ownerProgram,List.map_map,Function.comp_def,lifting,ownerFinish] using
      StringWrites.run_lift_string mode (StringInit.forms mode (ownerPC layout) layout.sentinel) (resetState mode layout state)
  have thirdRun : StringWrites.run mode ((Listing8FailComparison.program mode (comparison mode layout)).map StringStack.Form.previous)
      (ownerFinish mode layout state)=comparisonFinish mode layout state :=
    ControlPacketWrites.run mode _ _ (Listing8FailComparison.chain mode (comparison mode layout))
      (Listing8FailComparison.valid mode (comparison mode layout) (comparison_bounds mode layout bounds)) _
      (Listing8FailureReuseImage.comparison_entry mode layout bounds state entry current)
  rw [Listing8FailureTrace.program,List.map_append,List.map_append,List.map_append,
    StringWrites.owned_run_append,StringWrites.owned_run_append,StringWrites.owned_run_append]
  simp only [StringWrites.run_append,List.map_cons,List.map_nil,firstRun,secondRun,thirdRun]
  change ((_ ∧ _) ∧ _) ∧ StringWrites.OwnedRun mode codeStart codeEnd
    ((DwordPackets.program mode (post mode layout) (comparisonFinish mode layout state).principal).map (StringStoreWrites.liftDword mode)) _
  refine ⟨⟨⟨⟨first,trivial⟩,?_⟩,third⟩,last⟩
  simpa only [Listing8FailureTrace.ownerProgram,List.map_map,Function.comp_def,lifting] using second

theorem execute (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (bounds : Bounds mode layout)
    (placed : Placement mode codeStart codeEnd layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8FailureReuseImage.Current mode layout state.principal.memory) :
    StringStack.Trace mode state ((Listing8FailureTrace.program mode layout state).map StringStack.Form.previous)
      (finish mode layout state) ∧
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8FailureTrace.program mode layout state).map StringStack.Form.previous) state :=
  ⟨StringStack.previous_trace mode (Listing8FailureReuseEffects.trace mode layout bounds state entry current),
    owned mode codeStart codeEnd layout bounds placed state entry current⟩

end SmcTuring.Appendix.Listing8FailureReuseWrites

module
public import SmcTuring.Appendix.Listing8FailureTemplateFields
public import SmcTuring.Appendix.Listing8FailureReuseEffects

public section
namespace SmcTuring.Appendix.Listing8FailureTemplateRegions
open Native Listing8FailureLayout Listing8FailureImage Listing8FailureTemplateFields

theorem reset_field (mode : Mode) (l : Layout) (bounds : Listing8FailureBounds.Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) :
    Allowed mode l (StringWrites.packet mode (.previous (.previous (StringDwordArithmetic.canonical mode (reset mode l)))) state).address
      (StringWrites.packet mode (.previous (.previous (StringDwordArithmetic.canonical mode (reset mode l)))) state).bytes.length := by
  have coordinates:=positions mode l
  have capacity:=bounds.capacity
  have owned := MixedFieldOwnership.located mode l.start (mask mode l) (.store 0 0) state.principal rfl entry
    (by cases mode <;> simp [DwordArithmetic.length,Relocation.SignedDelta,Relocation.delta] at coordinates ⊢;omega)
    (by cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coordinates <;> omega)
    (Allowed mode l) (by simp [Allowed])
  change Allowed mode l (StringWrites.packet mode (StringStoreWrites.liftDword mode
      (StringMixed.canonical mode (.arithmetic (reset mode l)))) state).address
      (StringWrites.packet mode (StringStoreWrites.liftDword mode (StringMixed.canonical mode (.arithmetic (reset mode l)))) state).bytes.length
  simpa only [StringMixedWrites.address,StringMixedWrites.length,reset] using owned

/-- Static field geometry and present bytes derive every complete store in
the actual reset, initializer, WORD comparison and post-mask sequence. -/
theorem regions (mode : Mode) (l : Layout) (bounds : Listing8FailureBounds.Bounds mode l)
    (sentinelOutside : l.sentinel+mode.wordBytes≤l.start ∨ callPC mode l+5≤l.sentinel)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (current : Listing8FailureReuseImage.Current mode l state.principal.memory) :
    StringStoreRegions.Run mode (Allowed mode l)
      ((Listing8FailureTrace.program mode l state).map StringStack.Form.previous) state := by
  have first : StringStoreRegions.Run mode (Allowed mode l)
      [.previous (.previous (StringDwordArithmetic.canonical mode (reset mode l)))] state :=
    ⟨reset_field mode l bounds state entry,trivial⟩
  have second := StringStoreTemplateRuns.initializer mode (Allowed mode l) (ownerPC l) l.sentinel (resetState mode l state)
    (Listing8FailureImage.reset_pc mode l bounds state entry) (Listing8FailureBounds.owner_fits mode l bounds) bounds.sentinelFits
    (Listing8FailureReuseImage.reset_owner mode l bounds state entry current)
    (by simp [Allowed,source])
    (by rcases sentinelOutside with before | after
        · exact Or.inl before
        · exact Or.inr (Or.inl after))
  have third := StringStoreTemplateRuns.control mode (Allowed mode l) (Listing8FailComparison.sites mode (comparison mode l))
    (comparison mode l).start (Listing8FailComparison.chain mode (comparison mode l))
    (Listing8FailComparison.valid mode (comparison mode l) (Listing8FailureBounds.comparison_bounds mode l bounds))
    (comparison_fields mode l bounds) (ownerFinish mode l state)
    (Listing8FailureReuseImage.comparison_entry mode l bounds state entry current)
  have last := DwordXorRegionRuns.packets mode (Allowed mode l) (post mode l) (notPC mode l) (post_chain mode l)
    (Listing8FailureBounds.post_valid mode l bounds) (post_fields mode l) (comparisonFinish mode l state)
    (Listing8FailureReuseEffects.comparison_endpoint mode l bounds state entry current)
  have firstRun : StringWrites.run mode [.previous (.previous (StringDwordArithmetic.canonical mode (reset mode l)))] state=
      resetState mode l state := by
    change StringDword.execute mode (StringDwordArithmetic.canonical mode (reset mode l)) state=_
    rw [StringDwordArithmetic.execute];rfl
  have lifting : (fun form : StringForm.Form mode => StringStack.Form.previous (StringControl.Form.previous (StringDword.Form.string form)))=
      StringWrites.liftString mode := by funext form;rfl
  have secondRun : StringWrites.run mode ((Listing8FailureTrace.ownerProgram mode l).map StringStack.Form.previous)
      (resetState mode l state)=ownerFinish mode l state := by
    simpa only [Listing8FailureTrace.ownerProgram,List.map_map,Function.comp_def,lifting,ownerFinish] using
      StringWrites.run_lift_string mode (StringInit.forms mode (ownerPC l) l.sentinel) (resetState mode l state)
  have thirdRun : StringWrites.run mode ((Listing8FailComparison.program mode (comparison mode l)).map StringStack.Form.previous)
      (ownerFinish mode l state)=comparisonFinish mode l state :=
    ControlPacketWrites.run mode _ _ (Listing8FailComparison.chain mode (comparison mode l))
      (Listing8FailComparison.valid mode (comparison mode l) (Listing8FailureBounds.comparison_bounds mode l bounds)) _
      (Listing8FailureReuseImage.comparison_entry mode l bounds state entry current)
  rw [Listing8FailureTrace.program,List.map_append,List.map_append,List.map_append,
    StringStoreRegions.append,StringStoreRegions.append,StringStoreRegions.append]
  simp only [StringWrites.run_append,List.map_cons,List.map_nil,firstRun,secondRun,thirdRun]
  change ((_ ∧ _) ∧ _) ∧ StringStoreRegions.Run mode (Allowed mode l)
    ((DwordPackets.program mode (post mode l) (comparisonFinish mode l state).principal).map (StringStoreWrites.liftDword mode)) _
  refine ⟨⟨⟨first,?_⟩,third⟩,last⟩
  simpa only [Listing8FailureTrace.ownerProgram,List.map_map,Function.comp_def,lifting] using second

end SmcTuring.Appendix.Listing8FailureTemplateRegions

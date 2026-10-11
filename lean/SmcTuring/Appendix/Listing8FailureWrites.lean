module
public import SmcTuring.Appendix.Listing8FailureTrace
public import SmcTuring.Native.ControlPacketWrites
public import SmcTuring.Native.StringInitWrites
public import SmcTuring.Native.DwordPacketWrites
public import SmcTuring.Native.MixedLocatedWrites

public section
namespace SmcTuring.Appendix.Listing8FailureWrites
open Native Listing8FailureLayout Listing8FailureBounds Listing8FailureImage

structure Placement (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) : Prop where
  region : codeStart≤layout.start ∧ callPC mode layout+5≤codeEnd
  cursor : codeStart≤layout.cursor ∧ layout.cursor+mode.wordBytes≤codeEnd
  sentinel : codeStart≤layout.sentinel ∧ layout.sentinel+mode.wordBytes≤codeEnd

theorem fields (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (placed : Placement mode codeStart codeEnd layout) :
    (codeStart≤source mode layout ∧ source mode layout+mode.wordBytes≤codeEnd) ∧
    (codeStart≤mask mode layout ∧ mask mode layout+4≤codeEnd) := by
  have region:=placed.region
  have coords:=positions mode layout
  cases mode <;> simp [source,StringInit.field,StringCodec.fieldOffset,ownerPC,Mode.wordBytes] at region coords ⊢ <;> omega

theorem comparison_fields (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (placed : Placement mode codeStart codeEnd layout) :
    ∀ site∈Listing8FailComparison.sites mode (comparison mode layout),
      codeStart≤site.target ∧ site.target+ControlPackets.width mode site≤codeEnd := by
  have ⟨sourceInside,maskInside⟩:=fields mode codeStart codeEnd layout placed
  have cursorInside:=placed.cursor
  intro site member
  simp only [Listing8FailComparison.sites,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases mode <;> simp [Listing8FailComparison.site,Listing8FailComparison.target,Listing8FailComparison.operation,
    ControlPackets.width,comparison,Mode.wordBytes] at sourceInside maskInside cursorInside ⊢ <;> omega

theorem post_fields (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (placed : Placement mode codeStart codeEnd layout) :
    ∀ site∈post mode layout,codeStart≤site.target ∧ site.target+4≤codeEnd := by
  have region:=placed.region
  have coords:=positions mode layout
  intro site member
  simp only [post,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals cases mode <;> simp [callPC,endPC,xorPC,andPC,storePC,notPC,comparisonPC,ownerPC,stackSpan,
    StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,mask] at region coords ⊢ <;> omega

set_option maxHeartbeats 1000000 in
/-- The actual reset, DEFDATA, seven full-width comparison operations and
four live fail-mask/CALL-operand packets all store complete fields in code. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (bounds : Bounds mode layout)
    (placed : Placement mode codeStart codeEnd layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start) (initial : Initial mode layout state.principal.memory) :
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
    (reset_owner mode layout bounds state entry initial)
  have third:=ControlPacketWrites.owned mode codeStart codeEnd (Listing8FailComparison.sites mode (comparison mode layout))
    (comparison mode layout).start (Listing8FailComparison.chain mode (comparison mode layout))
    (Listing8FailComparison.valid mode (comparison mode layout) (comparison_bounds mode layout bounds))
    (comparison_fields mode codeStart codeEnd layout placed) (ownerFinish mode layout state)
    (comparison_entry mode layout bounds state entry initial)
  have last:=DwordPacketWrites.owned mode codeStart codeEnd (post mode layout) (notPC mode layout) (post_chain mode layout)
    (post_valid mode layout bounds) (post_fields mode codeStart codeEnd layout placed) (comparisonFinish mode layout state)
    (Listing8FailureTrace.comparison_endpoint mode layout bounds state entry initial)
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
      (comparison_entry mode layout bounds state entry initial)
  rw [Listing8FailureTrace.program,List.map_append,List.map_append,List.map_append,
    StringWrites.owned_run_append,StringWrites.owned_run_append,StringWrites.owned_run_append]
  simp only [StringWrites.run_append,List.map_cons,List.map_nil,firstRun,secondRun,thirdRun]
  change ((_ ∧ _) ∧ _) ∧ StringWrites.OwnedRun mode codeStart codeEnd
    ((DwordPackets.program mode (post mode layout) (comparisonFinish mode layout state).principal).map (StringStoreWrites.liftDword mode)) _
  refine ⟨⟨⟨⟨first,trivial⟩,?_⟩,third⟩,last⟩
  simpa only [Listing8FailureTrace.ownerProgram,List.map_map,Function.comp_def,lifting] using second

end SmcTuring.Appendix.Listing8FailureWrites

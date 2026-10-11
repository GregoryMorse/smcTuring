module
public import SmcTuring.Appendix.Listing8FailureImage

public section
namespace SmcTuring.Appendix.Listing8FailureTrace
open Native Listing8FailureLayout Listing8FailureBounds Listing8FailureImage
@[expose] def ownerProgram (mode : Mode) (l : Layout) :=
  (StringInit.forms mode (ownerPC l) l.sentinel).map (fun form => StringControl.Form.previous (.string form))
@[expose] def program (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  [StringControl.Form.previous (StringDwordArithmetic.canonical mode (reset mode l))] ++
    ownerProgram mode l ++ Listing8FailComparison.program mode (comparison mode l) ++
    (DwordPackets.program mode (post mode l) (comparisonFinish mode l state).principal).map StringControl.Form.previous

theorem comparison_endpoint (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    (comparisonFinish mode l state).principal.pc=Arithmetic.encodeNat mode (notPC mode l) :=
  Listing8FailComparison.endpoint mode (comparison mode l) _ (comparison_entry mode l bounds state entry initial)

theorem post_headers (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    DwordPackets.Intact mode (post mode l) (comparisonFinish mode l state).principal.memory := by
  intro reader member
  have outside:=mask_outside_post_headers mode l reader member
  rw [comparisonFinish,Listing8FailComparisonEffects.effect mode (comparison mode l) (comparison_bounds mode l bounds)
    (ownerFinish mode l state) (comparison_zero mode l bounds state entry initial)]
  change ByteMemory.bytesAt (DwordCode.put (ownerFinish mode l state).principal.memory (mask mode l) _) reader.pc 6 = _
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ outside,owner_effect mode l bounds state entry initial,
    reset_window mode l bounds state entry reader.pc 6 outside]
  exact post_initial mode l _ initial reader member

/-- The exact ordered reset, printed DEFDATA, USEWORD/COMPARE and fail-mask
packets share one state and fetch every instruction from current memory. -/
theorem trace (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    StringControl.Trace mode state (program mode l state) (finish mode l state) := by
  have startFits : l.start < 2^(8*mode.wordBytes) := by
    have cap:=bounds.capacity
    have coords:=positions mode l
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have fetched : StringControl.fetch mode state.principal.memory state.principal.pc.toNat=
      some (.previous (StringDwordArithmetic.canonical mode (reset mode l))) := by
    rw [entry,Arithmetic.encode_nat_toNat mode l.start startFits]
    exact StringControl.previous_fetch mode _ _ _ (StringDwordArithmetic.encoding mode _ _ _ (reset_current mode l _ initial))
  have first : StringControl.Trace mode state [.previous (StringDwordArithmetic.canonical mode (reset mode l))] (resetState mode l state) := by
    refine .step fetched ?_
    rw [StringControl.execute,StringDwordArithmetic.execute]
    exact .nil _
  have owner:=StringInitTrace.trace mode (ownerPC l) l.sentinel (resetState mode l state)
    (reset_pc mode l bounds state entry) (owner_fits mode l bounds) bounds.sentinelFits bounds.sentinelOutside
    (reset_owner mode l bounds state entry initial)
  have second : StringControl.Trace mode (resetState mode l state) (ownerProgram mode l) (ownerFinish mode l state) := by
    simpa only [ownerProgram,ownerFinish,List.map_map,Function.comp_def] using StringControl.previous_trace mode (StringDword.string_trace mode owner)
  have third:=Listing8FailComparison.trace mode (comparison mode l) (comparison_bounds mode l bounds) (ownerFinish mode l state)
    (comparison_entry mode l bounds state entry initial) (comparison_image mode l bounds state entry initial)
  have last:=StringControl.previous_trace mode (DwordPackets.trace mode (post mode l) (notPC mode l) (post_chain mode l)
    (post_valid mode l bounds) (post_outside_headers mode l) (comparisonFinish mode l state)
    (comparison_endpoint mode l bounds state entry initial) (post_headers mode l bounds state entry initial))
  exact StringControl.trace_append mode (StringControl.trace_append mode (StringControl.trace_append mode first second) third) last

theorem instruction_count (mode : Mode) (l : Layout) (state : StringExecution.State mode) :
    (program mode l state).length=if mode=.x86 then 13 else 16 := by
  simp only [program,List.length_append,List.length_cons,List.length_nil,List.length_map,
    Listing8FailComparison.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    (finish mode l state).principal.pc=Arithmetic.encodeNat mode (endPC mode l) := by
  have pc:=DwordPackets.endpoint mode (post mode l) (notPC mode l) (post_chain mode l) (post_valid mode l bounds)
    (comparisonFinish mode l state).principal (comparison_endpoint mode l bounds state entry initial)
  rw [post_span] at pc
  have position : notPC mode l+36=endPC mode l := by simp [endPC,xorPC,andPC,storePC,Nat.add_assoc]
  rw [position] at pc
  exact pc

end SmcTuring.Appendix.Listing8FailureTrace

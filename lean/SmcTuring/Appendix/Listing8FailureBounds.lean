module
public import SmcTuring.Appendix.Listing8FailureLayout

public section
namespace SmcTuring.Appendix.Listing8FailureBounds
open Native Listing8FailureLayout
structure Bounds (mode : Mode) (l : Layout) : Prop where
  capacity : callPC mode l+5 < 2^(8*mode.wordBytes)
  cursorBefore : l.cursor+mode.wordBytes ≤ l.start
  cursorNear : comparisonPC mode l ≤ l.cursor+2048
  sentinelFits : l.sentinel+mode.wordBytes < 2^(8*mode.wordBytes)
  sentinelOutside : l.sentinel+mode.wordBytes ≤ ownerPC l ∨ comparisonPC mode l ≤ l.sentinel

theorem comparison_bounds (mode : Mode) (l : Layout) (bounds : Bounds mode l) :
    Listing8FailComparison.Bounds mode (comparison mode l) := by
  have capacity:=bounds.capacity
  have before:=bounds.cursorBefore
  have near:=bounds.cursorNear
  have coords:=positions mode l
  have sourceEnd:=source_end mode l
  cases mode
  all_goals constructor
  all_goals simp [comparison,Listing8FailComparison.endPC,source,StringInit.field,StringCodec.fieldOffset,
    comparisonPC,ownerPC,WordMemoryArithmetic.size,wordPrefix,Mode.wordBytes,mask,xorPC,andPC,storePC,notPC,
    callPC,endPC,stackSpan,StringCodec.initialSize] at capacity before near coords sourceEnd ⊢ <;> omega

theorem reset_effect (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : Execution.State mode)
    (entry : state.pc=Arithmetic.encodeNat mode l.start) :
    DwordArithmetic.execute mode (reset mode l) state = {state with
      pc := Arithmetic.encodeNat mode (ownerPC l)
      memory := DwordCode.put state.memory (mask mode l) 0} := by
  have capacity:=bounds.capacity
  have coords:=positions mode l
  have range : mode=.x64 → Relocation.SignedDelta (l.start+10) (mask mode l) := by
    cases mode <;> simp [Relocation.SignedDelta,Relocation.delta] at coords ⊢ <;> omega
  have fits : mask mode l < 2^(8*mode.wordBytes) := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  exact DwordArithmetic.located_effect mode (.store 0 0) l.start (mask mode l) state rfl entry range fits

theorem owner_fits (mode : Mode) (l : Layout) (bounds : Bounds mode l) :
    ownerPC l+StringCodec.initialSize mode < 2^(8*mode.wordBytes) := by
  have cap:=bounds.capacity
  have coords:=positions mode l
  change comparisonPC mode l < _
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega

theorem post_valid (mode : Mode) (l : Layout) (bounds : Bounds mode l) :
    ∀ reader ∈ post mode l,DwordPackets.Valid mode reader := by
  intro reader member
  have cap:=bounds.capacity
  simp only [post,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals cases mode
  all_goals simp [DwordPackets.Valid,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,
    callPC,endPC,xorPC,andPC,storePC,notPC,comparisonPC,ownerPC,mask,stackSpan,
    StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,Relocation.SignedDelta,Relocation.delta,Mode.wordBytes] at cap ⊢ <;> omega

theorem post_outside_headers (mode : Mode) (l : Layout) : DwordPackets.OutsideHeaders (post mode l) := by
  intro writer wm reader rm
  simp only [post,List.mem_cons,List.not_mem_nil,or_false] at wm rm
  rcases wm with rfl | rfl | rfl | rfl
  all_goals rcases rm with rfl | rfl | rfl | rfl
  all_goals cases mode
  all_goals simp [callPC,endPC,xorPC,andPC,storePC,mask,stackSpan] <;> omega

theorem mask_outside_post_headers (mode : Mode) (l : Layout) (reader : DwordPackets.Site) (member : reader ∈ post mode l) :
    mask mode l+4 ≤ reader.pc ∨ reader.pc+6 ≤ mask mode l := by
  simp only [post,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals right
  all_goals simp [mask,xorPC,andPC,storePC] <;> omega

end SmcTuring.Appendix.Listing8FailureBounds

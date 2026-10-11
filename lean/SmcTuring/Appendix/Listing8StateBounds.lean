module
public import SmcTuring.Appendix.Listing8StateLayout

public section
namespace SmcTuring.Appendix.Listing8StateBounds
open Native Listing8StateLayout
structure Bounds (mode : Mode) (l : Layout) : Prop where
  capacity : endPC mode l < 2^(8*mode.wordBytes)
  cursorBefore : l.cursor+mode.wordBytes ≤ l.start
  cursorNear : l.start ≤ l.cursor+2048

theorem helper_valid (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (helper : DwordLayout.Layout) (member : helper ∈ helpers mode l) : DwordLayout.Admissible mode helper := by
  have cap := bounds.capacity;have before := bounds.cursorBefore;have near := bounds.cursorNear
  cases mode
  all_goals simp only [helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals constructor
  all_goals simp [endPC,updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.endPC,
    DwordLayout.thirdPC,DwordLayout.secondPC,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes,
    Relocation.SignedDelta,Relocation.delta] at cap before near ⊢ <;> omega

theorem helper_frames (mode : Mode) (l : Layout) : StringDwordSequence.OutsideCodes mode (helpers mode l) := by
  intro writer wm reader rm
  cases mode
  all_goals simp only [helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at wm rm
  all_goals rcases wm with rfl | rfl
  all_goals rcases rm with rfl | rfl
  all_goals right
  all_goals simp [updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.endPC,DwordLayout.thirdPC,
    DwordLayout.secondPC,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem packet_valid (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (site : DwordPackets.Site) (member : site ∈ packets mode l) : DwordPackets.Valid mode site := by
  have cap := bounds.capacity;have before := bounds.cursorBefore;have near := bounds.cursorNear
  cases mode
  all_goals simp only [packets,newPackets,masks,updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [DwordPackets.Valid,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,endPC,
    updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,
    Mode.wordBytes,Relocation.SignedDelta,Relocation.delta] at cap before near ⊢ <;> omega

theorem packet_frames (mode : Mode) (l : Layout) (bounds : Bounds mode l) : DwordPackets.OutsideHeaders (packets mode l) := by
  intro writer wm reader rm
  have before := bounds.cursorBefore
  cases mode
  all_goals simp only [packets,newPackets,masks,updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at wm rm
  all_goals rcases wm with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases rm with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,
    Mode.wordBytes] at before ⊢ <;> omega

theorem helpers_outside_headers (mode : Mode) (l : Layout) (writer : DwordLayout.Layout)
    (wm : writer ∈ helpers mode l) (reader : DwordPackets.Site) (rm : reader ∈ packets mode l) :
    writer.destination+4 ≤ reader.pc ∨ reader.pc+6 ≤ writer.destination := by
  cases mode
  all_goals simp only [helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at wm
  all_goals simp only [packets,newPackets,masks,updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at rm
  all_goals rcases wm with rfl | rfl
  all_goals rcases rm with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [updatePC,maskPC,newPC,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

end SmcTuring.Appendix.Listing8StateBounds

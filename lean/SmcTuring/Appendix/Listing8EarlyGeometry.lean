module
public import SmcTuring.Appendix.Listing8EarlyOwners
public import SmcTuring.Appendix.Listing8FailureGeometry

public section
namespace SmcTuring.Appendix.Listing8EarlyGeometry
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
theorem pointer_targets (mode : Mode) (l : Layout) (t : Targets) (copies : Listing8PointerCopies.Bounds mode l t)
    (writer : DwordLayout.Layout) (member : writer∈Listing8PointerCopies.layouts mode l t) : l.start ≤ writer.destination := by
  have main:=code_length mode l
  have endPC:=(Listing8PointerCopies.sizes mode l t).2.1
  have state:=copies.targetsAfter t.state (by simp)
  have back:=copies.targetsAfter t.back (by simp)
  have forward:=copies.targetsAfter t.forward (by simp)
  cases mode
  all_goals simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [reduceCtorEq,ite_true,ite_false] at endPC
  all_goals dsimp only
  all_goals omega

theorem direction_start (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8DirectionGeometry.Bounds mode l t) :
    l.start ≤ (Listing8DirectionGeometry.region mode l).start := by
  have locations:=Listing8InputBounds.positions mode l t bounds.input.fields bounds.input.joined
  change l.start ≤ Listing8LiteralInput.endPC mode l.input
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at locations <;> omega
theorem first_cursor (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8DirectionGeometry.Bounds mode l t) :
    l.start ≤ (Listing8DirectionGeometry.region mode l).cursor := by
  change l.start ≤ l.input.cursor
  rw [bounds.input.fields.cursorLabel]
  dsimp [StringCodec.sourceField];omega
theorem second_cursor (mode : Mode) (l : Layout) : l.start ≤ (Listing8StateGeometry.region mode l).cursor := by
  have lower:=endpoint_lower mode l.start (nodeSpan mode)
  change l.start ≤ secondStart mode l at lower
  change l.start ≤ StringCodec.sourceField mode (secondStart mode l)
  dsimp [StringCodec.sourceField];omega

theorem direction_helpers (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8DirectionGeometry.Bounds mode l t)
    (writer : DwordLayout.Layout) (member : writer∈Listing8DirectionLayout.helpers mode (Listing8DirectionGeometry.region mode l)) :
    l.start ≤ writer.destination := by
  have lower:=direction_start mode l t bounds
  cases mode
  all_goals simp only [Listing8DirectionLayout.helpers,Listing8DirectionLayout.duplicate,Listing8DirectionLayout.copy,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,
    Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] at * <;> omega
theorem direction_packets (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8DirectionGeometry.Bounds mode l t)
    (writer : DwordPackets.Site) (member : writer∈Listing8DirectionLayout.arithmetic mode (Listing8DirectionGeometry.region mode l)) :
    l.start ≤ writer.target := by
  have lower:=direction_start mode l t bounds
  cases mode
  all_goals simp only [Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,
    Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] at * <;> omega

theorem tail_xors (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8DirectionGeometry.Bounds mode l t)
    (writer : DwordXorHelper.Layout) (member : writer∈Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l)) :
    l.start ≤ writer.destination := by
  have lower:=direction_start mode l t bounds
  cases mode
  all_goals simp only [Listing8HeadTailBounds.xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,
    Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] at * <;> omega
theorem tail_packets (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8DirectionGeometry.Bounds mode l t)
    (writer : DwordPackets.Site) (member : writer∈Listing8DirectionLayout.masks mode (Listing8DirectionGeometry.region mode l)++
      Listing8DirectionLayout.heads mode (Listing8DirectionGeometry.region mode l)) : l.start ≤ writer.target := by
  have lower:=direction_start mode l t bounds
  have cursor:=first_cursor mode l t bounds
  cases mode
  all_goals simp only [Listing8DirectionLayout.masks,Listing8DirectionLayout.group,Listing8DirectionLayout.heads,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,
    Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount] at * <;> omega
end SmcTuring.Appendix.Listing8EarlyGeometry

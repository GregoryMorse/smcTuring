module
public import SmcTuring.Appendix.Listing8InputBodyFrames

public section
namespace SmcTuring.Appendix.Listing8DirectionWindows
open Native Listing8DirectionLayout
abbrev Targets:=Listing8PointerCopies.Targets
/-- The immutable helpers and opcode/address headers of the entire direction/head region. -/
@[expose] def windows (mode : Mode) (l : Layout) : List (Nat × Nat) :=
  [(l.start,if mode=.x86 then 17 else 54)] ++
    (arithmetic mode l).map (fun site => (site.pc,6)) ++
    [(selectionEnd mode l,if mode=.x86 then 18 else 36)] ++
    (masks mode l++heads mode l).map (fun site => (site.pc,6))

theorem helper_size (mode : Mode) (l : Layout) :
    (DwordMixedSequence.bytes mode (helpers mode l)).length=(if mode=.x86 then 17 else 54) := by
  cases mode <;> simp [DwordMixedSequence.bytes,helpers,duplicate,copy,DwordMixedImage.bytes_length,DwordLayout.span,DwordLayout.storeSize]

theorem xor_size (mode : Mode) (l : Layout) :
    (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode l)).length=(if mode=.x86 then 18 else 36) := by
  cases mode <;> simp [DwordXorSequence.bytes,Listing8HeadTailBounds.xorLayouts,DwordXorHelper.bytes_length]

theorem window_span (mode : Mode) (l : Layout) (w : Nat × Nat) (member : w∈windows mode l) :
    l.start≤w.1 ∧ w.1+w.2≤endPC mode l := by
  cases mode
  all_goals simp only [windows,arithmetic,group,masks,heads,List.map_append,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,ite_true,ite_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem helper_outside (mode : Mode) (l : Layout) (w : Nat × Nat) (member : w∈windows mode l)
    (writer : DwordLayout.Layout) (writerMember : writer∈helpers mode l) :
    writer.destination+4≤w.1 ∨ w.1+w.2≤writer.destination := by
  cases mode
  all_goals simp only [windows,arithmetic,group,masks,heads,List.map_append,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,ite_true,ite_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [helpers,duplicate,copy,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases writerMember with rfl | rfl | rfl
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem packet_outside (mode : Mode) (l : Layout) (w : Nat × Nat) (member : w∈windows mode l)
    (writer : DwordPackets.Site) (writerMember : writer∈arithmetic mode l) :
    writer.target+4≤w.1 ∨ w.1+w.2≤writer.target := by
  cases mode
  all_goals simp only [windows,arithmetic,group,masks,heads,List.map_append,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,ite_true,ite_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [arithmetic,group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases writerMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem xor_outside (mode : Mode) (l : Layout) (w : Nat × Nat) (member : w∈windows mode l)
    (writer : DwordXorHelper.Layout) (writerMember : writer∈Listing8HeadTailBounds.xorLayouts mode l) :
    writer.destination+4≤w.1 ∨ w.1+w.2≤writer.destination := by
  cases mode
  all_goals simp only [windows,arithmetic,group,masks,heads,List.map_append,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,ite_true,ite_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Listing8HeadTailBounds.xorLayouts,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases writerMember with rfl | rfl
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem tail_outside (mode : Mode) (l : Layout) (cursorBefore : l.cursor+mode.wordBytes≤l.start)
    (w : Nat × Nat) (member : w∈windows mode l) (writer : DwordPackets.Site)
    (writerMember : writer∈masks mode l++heads mode l) :
    writer.target+4≤w.1 ∨ w.1+w.2≤writer.target := by
  cases mode
  all_goals simp only [windows,arithmetic,group,masks,heads,List.map_append,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,ite_true,ite_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [masks,group,heads,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals rcases writerMember with rfl | rfl | rfl | rfl
  all_goals simp only [Mode.wordBytes] at cursorBefore
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

end SmcTuring.Appendix.Listing8DirectionWindows

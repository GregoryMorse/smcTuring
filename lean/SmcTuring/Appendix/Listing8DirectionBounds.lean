module
public import SmcTuring.Appendix.Listing8DirectionLayout

public section
namespace SmcTuring.Appendix.Listing8DirectionBounds
open Native Listing8DirectionLayout

theorem helper_valid (mode : Mode) (l : Layout) (capacity : endPC mode l < 2^(8*mode.wordBytes))
    (helper : DwordLayout.Layout) (member : helper ∈ helpers mode l) : DwordLayout.Admissible mode helper := by
  cases mode
  all_goals simp only [helpers,duplicate,copy,List.nil_append,List.cons_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals constructor
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.endPC,DwordLayout.thirdPC,
    DwordLayout.secondPC,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes,
    Relocation.SignedDelta,Relocation.delta] at capacity ⊢ <;> omega

theorem helper_frames (mode : Mode) (l : Layout) : StringDwordSequence.OutsideCodes mode (helpers mode l) := by
  intro writer writerMember reader readerMember
  cases mode
  all_goals simp only [helpers,duplicate,copy,List.nil_append,List.cons_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember readerMember
  all_goals rcases writerMember with rfl | rfl | rfl
  all_goals rcases readerMember with rfl | rfl | rfl
  all_goals right
  all_goals simp [directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.endPC,DwordLayout.thirdPC,
    DwordLayout.secondPC,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem arithmetic_valid (mode : Mode) (l : Layout) (capacity : endPC mode l < 2^(8*mode.wordBytes))
    (site : DwordPackets.Site) (member : site ∈ arithmetic mode l) : DwordPackets.Valid mode site := by
  cases mode
  all_goals simp only [arithmetic,group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [DwordPackets.Valid,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,
    endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,
    Mode.wordBytes,Relocation.SignedDelta,Relocation.delta] at capacity ⊢ <;> omega

theorem arithmetic_frames (mode : Mode) (l : Layout) : DwordPackets.OutsideHeaders (arithmetic mode l) := by
  intro writer writerMember reader readerMember
  cases mode
  all_goals simp only [arithmetic,group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember readerMember
  all_goals rcases writerMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases readerMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem helpers_outside_headers (mode : Mode) (l : Layout) (writer : DwordLayout.Layout)
    (writerMember : writer ∈ helpers mode l) (reader : DwordPackets.Site) (readerMember : reader ∈ arithmetic mode l) :
    writer.destination+4 ≤ reader.pc ∨ reader.pc+6 ≤ writer.destination := by
  cases mode
  all_goals simp only [helpers,duplicate,copy,List.nil_append,List.cons_append,List.mem_cons,List.not_mem_nil,or_false] at writerMember
  all_goals simp only [arithmetic,group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at readerMember
  all_goals rcases writerMember with rfl | rfl | rfl
  all_goals rcases readerMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

end SmcTuring.Appendix.Listing8DirectionBounds

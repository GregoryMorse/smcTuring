module
public import SmcTuring.Appendix.Listing8HeadTailBounds

public section
namespace SmcTuring.Appendix.Listing8HeadTailFrames
open Native Listing8DirectionLayout Listing8HeadTailBounds

theorem xor_headers (mode : Mode) (l : Layout) (writer : DwordXorHelper.Layout)
    (member : writer ∈ xorLayouts mode l) (reader : DwordPackets.Site)
    (readerMember : reader ∈ masks mode l ++ heads mode l) :
    writer.destination+4 ≤ reader.pc ∨ reader.pc+6 ≤ writer.destination := by
  cases mode
  all_goals simp only [xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals simp only [masks,heads,group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at readerMember
  all_goals rcases member with rfl | rfl
  all_goals rcases readerMember with rfl | rfl | rfl | rfl
  all_goals simp [directionPC,maskPC,halves,Listing8PointerCopies.halfCount] <;> omega

theorem mask_headers (mode : Mode) (l : Layout) (writer : DwordPackets.Site)
    (member : writer ∈ masks mode l) (reader : DwordPackets.Site)
    (readerMember : reader ∈ heads mode l) :
    writer.target+4 ≤ reader.pc ∨ reader.pc+6 ≤ writer.target := by
  cases mode
  all_goals simp only [masks,group,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals simp only [heads,List.mem_cons,List.not_mem_nil,or_false] at readerMember
  all_goals rcases member with rfl | rfl
  all_goals rcases readerMember with rfl | rfl
  all_goals simp [directionPC,halves,Listing8PointerCopies.halfCount] <;> omega

theorem xor_span (mode : Mode) (l : Layout) :
    selectionEnd mode l+(xorLayouts mode l).length*18 = maskPC mode l := by
  cases mode <;> simp [xorLayouts,maskPC,halves,Listing8PointerCopies.halfCount]

theorem mask_span (mode : Mode) (l : Layout) :
    maskPC mode l+((masks mode l).map DwordPackets.size).sum = directionPC mode l := by
  cases mode <;> simp [masks,group,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,
    directionPC,halves,Listing8PointerCopies.halfCount]

theorem head_span (mode : Mode) (l : Layout) :
    directionPC mode l+((heads mode l).map DwordPackets.size).sum = endPC mode l := by
  cases mode <;> simp [heads,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,
    endPC,halves,Listing8PointerCopies.halfCount]

theorem selection_span (mode : Mode) (l : Layout) :
    l.start+(DwordMixedSequence.bytes mode (helpers mode l) ++ packets mode (arithmetic mode l)).length = selectionEnd mode l := by
  cases mode <;> simp [DwordMixedSequence.bytes,helpers,duplicate,copy,arithmetic,group,
    DwordMixedImage.bytes_length,packet_lengths,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,
    selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,duplicateSpan,halves,
    Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc]

theorem xor_length (mode : Mode) (l : Layout) :
    (DwordXorSequence.bytes mode (xorLayouts mode l)).length = if mode = .x86 then 18 else 36 := by
  cases mode <;> rfl

theorem prefix_span (mode : Mode) (l : Layout) :
    l.start+(DwordMixedSequence.bytes mode (helpers mode l) ++ packets mode (arithmetic mode l) ++ differences mode l).length = maskPC mode l := by
  have selection := selection_span mode l
  rw [←xor_bytes,List.length_append,List.length_append,xor_length]
  simp only [List.length_append] at selection
  have location := xor_span mode l
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,xorLayouts,List.length_cons,List.length_nil] at location ⊢ <;> omega

theorem headers_chain (mode : Mode) (l : Layout) :
    DwordPackets.Contiguous (maskPC mode l) (masks mode l ++ heads mode l) := by
  cases mode <;> simp [masks,heads,group,DwordPackets.Contiguous,DwordPackets.size,DwordPackets.raw,
    DwordArithmetic.length,directionPC,halves,Listing8PointerCopies.halfCount,Nat.add_assoc]

end SmcTuring.Appendix.Listing8HeadTailFrames

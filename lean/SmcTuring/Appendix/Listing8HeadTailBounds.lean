module
public import SmcTuring.Native.DwordXorSequence
public import SmcTuring.Appendix.Listing8DirectionSelected

public section
namespace SmcTuring.Appendix.Listing8HeadTailBounds
open Native Listing8DirectionLayout
@[expose] def xorLayouts (mode : Mode) (l : Layout) : List DwordXorHelper.Layout :=
  match mode with
  | .x86 => [⟨selectionEnd mode l,l.cursor,directionPC mode l+6⟩]
  | .x64 => [⟨selectionEnd mode l,l.cursor,directionPC mode l+6⟩,
      ⟨selectionEnd mode l+18,l.cursor+4,directionPC mode l+16⟩]
/-- Initial finite placement only. The actual global cursor lies within
2048 bytes before this region; all signed reaches then follow. -/
structure Bounds (mode : Mode) (l : Layout) : Prop where
  capacity : endPC mode l < 2^(8*mode.wordBytes)
  cursorBefore : l.cursor+mode.wordBytes ≤ l.start
  cursorNear : l.start ≤ l.cursor+2048

theorem xor_chain (mode : Mode) (l : Layout) : DwordXorSequence.Contiguous (selectionEnd mode l) (xorLayouts mode l) := by
  cases mode <;> simp [xorLayouts,DwordXorSequence.Contiguous,DwordXorHelper.endPC]

theorem xor_bytes (mode : Mode) (l : Layout) :
    DwordXorSequence.bytes mode (xorLayouts mode l) = differences mode l := by
  cases mode <;> simp [DwordXorSequence.bytes,xorLayouts,DwordXorHelper.bytes,DwordXorHelper.first,
    DwordXorHelper.middle,DwordXorHelper.third,DwordXorHelper.endPC,DwordCode.encode,DwordXor.encode,
    differences,differenceBytes,Native.encode,MemoryOp.prefix,MemoryOp.tag,MemoryOp.trailer,wordPrefix,List.append_assoc]

theorem xor_valid (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (helper : DwordXorHelper.Layout) (member : helper ∈ xorLayouts mode l) : DwordXorHelper.Admissible mode helper := by
  have cap := bounds.capacity;have before := bounds.cursorBefore;have near := bounds.cursorNear
  cases mode
  all_goals simp only [xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals constructor
  all_goals simp [endPC,directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,
    duplicateSpan,halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,
    DwordXorHelper.endPC,Mode.wordBytes,Relocation.SignedDelta,Relocation.delta] at cap before near ⊢ <;> omega

theorem xor_frames (mode : Mode) (l : Layout) : DwordXorSequence.OutsideCodes (xorLayouts mode l) := by
  intro writer writerMember reader readerMember
  cases mode
  all_goals simp only [xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at writerMember readerMember
  all_goals rcases writerMember with rfl | rfl
  all_goals rcases readerMember with rfl | rfl
  all_goals right
  all_goals simp [directionPC,maskPC,halves,Listing8PointerCopies.halfCount,DwordXorHelper.endPC] <;> omega

theorem masks_chain (mode : Mode) (l : Layout) : DwordPackets.Contiguous (maskPC mode l) (masks mode l) := by
  cases mode <;> simp [masks,group,DwordPackets.Contiguous,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length]

theorem heads_chain (mode : Mode) (l : Layout) : DwordPackets.Contiguous (directionPC mode l) (heads mode l) := by
  cases mode <;> simp [heads,DwordPackets.Contiguous,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length]

theorem packets_valid (mode : Mode) (l : Layout) (bounds : Bounds mode l) (site : DwordPackets.Site)
    (member : site ∈ masks mode l ++ heads mode l) : DwordPackets.Valid mode site := by
  have cap := bounds.capacity;have before := bounds.cursorBefore;have near := bounds.cursorNear
  cases mode
  all_goals simp only [masks,heads,group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals simp [DwordPackets.Valid,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,endPC,
    directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,duplicateSpan,halves,
    Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes,
    Relocation.SignedDelta,Relocation.delta] at cap before near ⊢ <;> omega

theorem masks_frames (mode : Mode) (l : Layout) : DwordPackets.OutsideHeaders (masks mode l) := by
  intro writer writerMember reader readerMember
  cases mode
  all_goals simp only [masks,group,List.mem_cons,List.not_mem_nil,or_false] at writerMember readerMember
  all_goals rcases writerMember with rfl | rfl
  all_goals rcases readerMember with rfl | rfl
  all_goals right
  all_goals simp [directionPC,halves,Listing8PointerCopies.halfCount] <;> omega

theorem heads_frames (mode : Mode) (l : Layout) (bounds : Bounds mode l) : DwordPackets.OutsideHeaders (heads mode l) := by
  intro writer writerMember reader readerMember
  have before := bounds.cursorBefore
  cases mode
  all_goals simp only [heads,List.mem_cons,List.not_mem_nil,or_false] at writerMember readerMember
  all_goals rcases writerMember with rfl | rfl
  all_goals rcases readerMember with rfl | rfl
  all_goals left
  all_goals simp [directionPC,maskPC,selectionEnd,combinedPC,forwardPC,notPC,backPC,copyStart,duplicateSpan,
    halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at before ⊢ <;> omega

end SmcTuring.Appendix.Listing8HeadTailBounds

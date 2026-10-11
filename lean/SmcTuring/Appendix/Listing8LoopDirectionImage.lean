module
public import SmcTuring.Appendix.Listing8DirectionWindows
public import SmcTuring.Appendix.Listing8HeadTailTrace

public section
namespace SmcTuring.Appendix.Listing8LoopDirectionImage
open Native Listing8DirectionLayout

/-- Present immutable direction/head fragments. The mutable direction,
neighbor, match-mask and cursor operands are intentionally not fields. -/
structure Current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) : Prop where
  helpers : ByteMemory.bytesAt memory l.start (DwordMixedSequence.bytes mode (helpers mode l)).length=DwordMixedSequence.bytes mode (helpers mode l)
  arithmetic : DwordPackets.Intact mode (arithmetic mode l) memory
  xorImage : ByteMemory.bytesAt memory (selectionEnd mode l)
    (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode l)).length=DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode l)
  tailHeaders : DwordPackets.Intact mode (masks mode l++heads mode l) memory

theorem helper_member (mode : Mode) (l : Layout) :
    (l.start,(DwordMixedSequence.bytes mode (helpers mode l)).length)∈Listing8DirectionWindows.windows mode l := by
  simp [Listing8DirectionWindows.windows,Listing8DirectionWindows.helper_size]

theorem arithmetic_member (mode : Mode) (l : Layout) (reader : DwordPackets.Site) (member : reader∈arithmetic mode l) :
    (reader.pc,6)∈Listing8DirectionWindows.windows mode l := by
  simp only [Listing8DirectionWindows.windows,List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨reader,member,rfl⟩)))

theorem xor_member (mode : Mode) (l : Layout) :
    (selectionEnd mode l,(DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode l)).length)∈Listing8DirectionWindows.windows mode l := by
  simp [Listing8DirectionWindows.windows,Listing8DirectionWindows.xor_size]

theorem tail_member (mode : Mode) (l : Layout) (reader : DwordPackets.Site) (member : reader∈masks mode l++heads mode l) :
    (reader.pc,6)∈Listing8DirectionWindows.windows mode l := by
  simp only [Listing8DirectionWindows.windows,List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨reader,member,rfl⟩)

/-- Equality on the positively enumerated immutable byte windows transfers
all current instruction fragments, independently of their live operands. -/
theorem transport (mode : Mode) (l : Layout) (before after : ByteMemory.Memory) (current : Current mode l before)
    (frames : ∀ w∈Listing8DirectionWindows.windows mode l,ByteMemory.bytesAt after w.1 w.2=ByteMemory.bytesAt before w.1 w.2) :
    Current mode l after := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [frames _ (helper_member mode l)]
    exact current.helpers
  · intro reader member
    rw [DwordPackets.Current,frames _ (arithmetic_member mode l reader member)]
    exact current.arithmetic reader member
  · rw [frames _ (xor_member mode l)]
    exact current.xorImage
  · intro reader member
    rw [DwordPackets.Current,frames _ (tail_member mode l reader member)]
    exact current.tailHeaders reader member

end SmcTuring.Appendix.Listing8LoopDirectionImage

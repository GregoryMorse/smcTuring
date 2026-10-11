module
public import SmcTuring.Appendix.Listing8StateReuseFrames

public section
namespace SmcTuring.Appendix.Listing8LoopStateImage
open Native Listing8StateLayout

/-- Immutable state helper bytes and instruction headers in present memory.
The new-state, match-mask and transition-cursor operands remain live. -/
structure Current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) : Prop where
  helpers : ByteMemory.bytesAt memory l.start (DwordMixedSequence.bytes mode (helpers mode l)).length=DwordMixedSequence.bytes mode (helpers mode l)
  headers : DwordPackets.Intact mode (packets mode l) memory

theorem helper_member (mode : Mode) (l : Layout) :
    (l.start,(DwordMixedSequence.bytes mode (helpers mode l)).length)∈Listing8StateGeometry.windows mode l := by
  cases mode <;> simp [Listing8StateGeometry.windows,DwordMixedSequence.bytes,helpers,Listing8PointerCopies.split,
    DwordMixedImage.bytes_length,DwordLayout.span,DwordLayout.storeSize]

theorem header_member (mode : Mode) (l : Layout) (reader : DwordPackets.Site) (member : reader∈packets mode l) :
    (reader.pc,6)∈Listing8StateGeometry.windows mode l := by
  cases mode
  all_goals simp only [packets,newPackets,masks,updates,Listing8DirectionLayout.group,
    List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8StateGeometry.windows]

theorem transport (mode : Mode) (l : Layout) (before after : ByteMemory.Memory) (current : Current mode l before)
    (frames : ∀ w∈Listing8StateGeometry.windows mode l,ByteMemory.bytesAt after w.1 w.2=ByteMemory.bytesAt before w.1 w.2) :
    Current mode l after := by
  refine ⟨?_,?_⟩
  · rw [frames _ (helper_member mode l)]
    exact current.helpers
  · intro reader member
    rw [DwordPackets.Current,frames _ (header_member mode l reader member)]
    exact current.headers reader member

end SmcTuring.Appendix.Listing8LoopStateImage

module
public import SmcTuring.Appendix.Listing8InputMaskEffects

public section
namespace SmcTuring.Appendix.Listing8InputWindows
open Native Listing8LiteralInput
abbrev Dword := BitVec 32
structure Outside (mode : Mode) (l : Layout) (observed count : Nat) : Prop where
  scalar : scalarField mode l+4 ≤ observed ∨ observed+count ≤ scalarField mode l
  mask : maskField mode l+4 ≤ observed ∨ observed+count ≤ maskField mode l
  pending : pendingField mode l+4 ≤ observed ∨ observed+count ≤ pendingField mode l
  tape : l.head+10 ≤ observed ∨ observed+count ≤ l.head+6
  destinations : ∀ helper ∈ distributionLayouts mode l,
    helper.destination+4 ≤ observed ∨ observed+count ≤ helper.destination

/-- The exact input-region effects preserve each static disjoint window,
including future headers whose immediate fields receive copied masks. -/
theorem window (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.memory)
    (bound : MixedMemory.getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (value : DwordCode.get state.memory (layout.head+6) = tape)
    (observed count : Nat) (disjoint : Outside mode layout observed count) :
    ByteMemory.bytesAt (Listing8LiteralComposition.finish mode layout rule tape fresh state).memory observed count =
      ByteMemory.bytesAt state.memory observed count := by
  have intact := Listing8InputMask.zero_intact mode layout rule tape pending fresh oldMask state.memory current
  have cursor := (Listing8InputMaskEffects.cursor mode layout outside state).trans bound
  have symbol := (Listing8InputMaskEffects.symbol mode layout outside state).trans value
  rw [Listing8InputMask.finish_same mode layout rule tape fresh capacity state entry,
    Listing8SourceEffects.effect mode layout rule tape pending fresh capacity masks update outside
      (Listing8InputMask.normalized mode layout state) entry intact cursor symbol]
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ disjoint.tape,DwordMixedImage.bytes_frame _ _ _ _ _ disjoint.pending,
    Listing8LiteralComposition.distribution_memory mode layout rule tape pending fresh capacity masks
      (Listing8InputMask.normalized mode layout state) entry intact,
    DwordMixedSequence.putFields_window _ _ _ observed count disjoint.destinations,
    prefix_effect mode layout rule tape pending fresh capacity (Listing8InputMask.normalized mode layout state) entry intact]
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ disjoint.mask,DwordMixedImage.bytes_frame _ _ _ _ _ disjoint.scalar,
    DwordMixedImage.bytes_frame _ _ _ _ _ disjoint.pending,DwordMixedImage.bytes_frame _ _ _ _ _ disjoint.mask]
  exact DwordMixedImage.bytes_frame state.memory _ observed count 0 disjoint.mask

end SmcTuring.Appendix.Listing8InputWindows

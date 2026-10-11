module
public import SmcTuring.Appendix.Listing8PointerCopies
public import SmcTuring.Appendix.Listing8OwnerInput

public section
namespace SmcTuring.Appendix.Listing8PointerImage
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets := Listing8PointerCopies.Targets

@[expose] def backing (mode : Mode) (l : Layout) (t : Targets) (extra : ByteMemory.Memory) :=
  ByteMemory.putBytes extra (codeEnd mode l) (Listing8PointerCopies.bytes mode l t)
@[expose] def ownerFinish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8CopiedOwners.finish mode l v (backing mode l t extra) seed
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8PointerCopies.finish mode l t (ownerFinish mode l t v extra seed)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :=
  Listing8CopiedOwners.program mode l v ++ Listing8PointerCopies.program mode l t

/-- Complete future windows in the gap are preserved by the actual two
copies, four retargets, tape store and every copied owner. Pointer owners
restore their entire temporary memory writes before the later fetch. -/
theorem prefix_window (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (lower : codeEnd mode l ≤ observed) (upper : observed+count ≤ l.input.start) :
    ByteMemory.bytesAt (Listing8CopiedOwners.finish mode l v extra seed).principal.memory observed count =
      ByteMemory.bytesAt (image mode l v extra) observed count := by
  have inputFields := Listing8CopiedOwners.scalar_bounds mode l
  have sourceField := Listing8OwnerImage.source_field_bounds mode l
  have inputEnd : l.input.start ≤ Listing8LiteralInput.endPC mode l.input := by
    have h := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at h <;> omega
  rw [(Listing8CopiedOwners.result mode l v r b extra seed).2.1]
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by have after := b.directionAfter;omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by omega))]
  have patches : ∀ site ∈ Listing8ModeOffsets.sites mode (patchLayout mode l),
      site.owner+6 ≤ observed ∨ observed+count ≤ site.owner+2 := by
    intro site member
    simp only [Listing8ModeOffsets.sites,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> left <;>
      cases mode <;> simp [patchLayout,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,
        codeEnd,Listing8ModeOffsets.endPC,directionEntry,newEntry,currentEntry,nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize] at lower ⊢ <;> omega
  rw [Listing8OwnerImage.frame mode l v r b.tapeReach extra seed observed count patches (Or.inr (by omega)),
    Listing8CopyTrace.second_effect mode l v r extra seed,Listing8CopyTrace.first_effect mode l v r extra seed]
  have nodeLength : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have transLength : (sourceTransitionBytes mode l v).length = transitionSpan mode := transition_length mode _ _ _ _ _ _
  rw [byte_frame _ _ _ _ _ (Or.inl (by rw [transLength];have d := (destinations mode l).2.2;omega)),
    byte_frame _ _ _ _ _ (Or.inl (by rw [nodeLength];have d := destinations mode l;omega))]
  rfl

theorem initial_helper (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (joined : l.input.start = Listing8PointerCopies.endPC mode l) (extra : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode l v (backing mode l t extra)) (codeEnd mode l)
      (Listing8PointerCopies.bytes mode l t).length = Listing8PointerCopies.bytes mode l t := by
  have ending := Listing8PointerCopies.bytes_length mode l t
  have main := code_length mode l
  have inputEnd : l.input.start ≤ Listing8LiteralInput.endPC mode l.input := by
    have h := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at h <;> omega
  have exterior (source size : Nat)
      (outside : source+size ≤ l.start ∨ Listing8LiteralInput.endPC mode l.input ≤ source) :
      source+size ≤ codeEnd mode l ∨ codeEnd mode l+(Listing8PointerCopies.bytes mode l t).length ≤ source := by
    rcases outside with early | late
    · left;omega
    · right;omega
  unfold image
  rw [byte_frame _ _ _ _ _ (by rw [show (sourceTransitionBytes mode l v).length = transitionSpan mode from transition_length mode _ _ _ _ _ _];exact exterior _ _ r.transitionOutside),
    byte_frame _ _ _ _ _ (by rw [show (sourceNodeBytes mode l v).length = nodeSpan mode from node_length mode _ _ _ _];exact exterior _ _ r.nodeOutside),
    byte_frame _ _ _ _ _ (Or.inl (by omega)),
    byte_frame _ _ _ _ _ (Or.inr (by omega))]
  exact ByteMemory.bytes_at_put _ _ _

theorem helper_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (joined : l.input.start = Listing8PointerCopies.endPC mode l)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (ownerFinish mode l t v extra seed).principal.memory (codeEnd mode l)
      (Listing8PointerCopies.bytes mode l t).length = Listing8PointerCopies.bytes mode l t := by
  rw [ownerFinish,prefix_window mode l v r b _ seed _ _ (Nat.le_refl _) (by rw [Listing8PointerCopies.bytes_length,joined])]
  exact initial_helper mode l t v r joined extra

/-- One initialized image and one deterministic decoder now execute both
TRANSFERDATA calls, patches, all copied owners and all four pointer copies.
The helper image at its reached entry is a conclusion, not a premise. -/
theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (joined : l.input.start = Listing8PointerCopies.endPC mode l)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (initial mode l v (backing mode l t extra) seed)
      (program mode l t v) (finish mode l t v extra seed) := by
  exact StringDword.trace_append mode (Listing8CopiedOwners.trace mode l v r b _ seed)
    (Listing8PointerCopies.trace mode l t copies _ (Listing8CopiedOwners.result mode l v r b _ seed).1
      (helper_current mode l t v r b joined extra seed))

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :
    (program mode l t v).length = if mode = .x86 then 81 else 92 := by
  rw [program,List.length_append,Listing8CopiedOwners.instruction_count,(Listing8PointerCopies.sizes mode l t).2.2]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (joined : l.input.start = Listing8PointerCopies.endPC mode l)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l t v extra seed).principal.pc = Arithmetic.encodeNat mode l.input.start := by
  rw [finish,ownerFinish,Listing8PointerCopies.endpoint mode l t copies _
    (Listing8CopiedOwners.result mode l v r b _ seed).1,joined]

end SmcTuring.Appendix.Listing8PointerImage

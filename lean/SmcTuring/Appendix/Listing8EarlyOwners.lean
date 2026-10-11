module
public import SmcTuring.Appendix.Listing8GlobalWindows

public section
namespace SmcTuring.Appendix.Listing8EarlyOwners
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
theorem patch_after (mode : Mode) (l : Layout) : l.start ≤ patchStart mode l := by
  have a:=endpoint_lower mode l.start (nodeSpan mode)
  have b:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change l.start ≤ secondStart mode l at a
  change secondStart mode l ≤ patchStart mode l at b
  exact Nat.le_trans a b
theorem input_after (mode : Mode) (l : Layout) (r : Resources mode l) : l.start ≤ l.input.start := by
  have code:=code_length mode l
  have after:=r.inputAfter
  omega

/-- Actual copies, retargets, tape operand write and copied owners preserve
all earlier windows. Pointer-owner temporary exchanges restore whole memory. -/
theorem owners (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (bounds : Listing8CopiedOwners.Bounds mode l v) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count ≤ l.start) :
    ByteMemory.bytesAt (Listing8CopiedOwners.finish mode l v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (image mode l v extra) observed count := by
  have input:=input_after mode l r
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have inputEnd : l.input.start ≤ Listing8LiteralInput.endPC mode l.input := by
    have coords:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have direction:=bounds.directionAfter
  rw [(Listing8CopiedOwners.result mode l v r bounds extra seed).2.1,
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by omega))]
  have patches : ∀ site∈Listing8ModeOffsets.sites mode (patchLayout mode l),
      site.owner+6 ≤ observed ∨ observed+count ≤ site.owner+2 := by
    intro site member
    have located:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).1
    change patchStart mode l+40 ≤ site.owner at located
    have lower:=patch_after mode l
    exact Or.inr (by omega)
  rw [Listing8OwnerImage.frame mode l v r bounds.tapeReach extra seed observed count patches (Or.inr (by omega)),
    Listing8CopyTrace.second_effect mode l v r extra seed,Listing8CopyTrace.first_effect mode l v r extra seed]
  have destinations:=destinations mode l
  rw [byte_frame _ _ _ _ _ (Or.inr (by omega)),byte_frame _ _ _ _ _ (Or.inr (by omega))]
  rfl

theorem pointers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (bounds : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (before : observed+count ≤ l.start)
    (targets : ∀ helper∈Listing8PointerCopies.layouts mode l t, l.start ≤ helper.destination) :
    ByteMemory.bytesAt (Listing8PointerImage.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (image mode l v (Listing8PointerImage.backing mode l t extra)) observed count := by
  have prior:=(Listing8CopiedOwners.result mode l v r bounds (Listing8PointerImage.backing mode l t extra) seed).1
  have cursorBefore : l.start ≤ (Listing8PointerCopies.word mode l).destination := by
    have after:=endpoint_lower mode l.start (nodeSpan mode)
    change l.start ≤ secondStart mode l at after
    change l.start ≤ StringCodec.sourceField mode (secondStart mode l)
    dsimp [StringCodec.sourceField];omega
  rw [Listing8PointerImage.finish,Listing8PointerImage.ownerFinish,Listing8PointerCopies.window_frame mode l t copies _ prior observed count
    (Or.inr (by omega)) (fun writer member => Or.inr (Nat.le_trans before (targets writer member)))]
  exact owners mode l v r bounds (Listing8PointerImage.backing mode l t extra) seed observed count before
end SmcTuring.Appendix.Listing8EarlyOwners

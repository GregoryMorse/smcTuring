module
public import SmcTuring.Appendix.Listing8FailLayout

public section
namespace SmcTuring.Appendix.Listing8FailImage
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def backing (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) :=
  ByteMemory.putBytes memory (Listing8JumpLayout.failPC mode origin) (Listing8FailLayout.bytes mode origin)
/-- Arbitrarily later bounded windows retain the original backing bytes after
the complete actual body, under static separation from both source templates. -/
theorem body_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel limit : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (tail : Listing8FailLayout.Bounds mode origin l limit)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat)
    (after : Listing8JumpLayout.failPC mode origin ≤ observed) (upper : observed+count ≤ limit) :
    ByteMemory.bytesAt (Listing8GlobalJump.bodyEnd mode origin l t v sentinel memory seed).principal.memory observed count=
      ByteMemory.bytesAt memory observed count := by
  have sources:=Listing8FailLayout.source_windows mode origin l limit tail observed count after upper
  have large : 10 ≤ nodeSpan mode := by cases mode <;> decide
  have tapeOutside : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6 := by
    rcases sources.1 with early | late
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have afterCall : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin))+5 ≤ observed := by
    change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l sentinel)+5 ≤ observed
    rw [Listing8JumpImage.call_position mode origin l t sentinel boot body];exact after
  have coords:=Listing8FailureLayout.positions mode (Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin))
  have afterRegion : (Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin)).start ≤ observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have bootBefore : origin+Listing4EntryLayout.size mode ≤ observed := by
    have location:=(Listing8JumpLayout.positions mode origin).2
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at location <;> dsimp [Listing4EntryLayout.size] <;> omega
  have prefixBefore : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length ≤ observed := by
    rw [Listing8JumpLayout.prefix_length]
    change Listing8JumpLayout.callPC mode origin ≤ observed
    dsimp [Listing8JumpLayout.failPC] at after;omega
  rw [Listing8GlobalJump.bodyEnd,Listing8GlobalBoot.finish,
    Listing8LateFrames.after_failure mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _ observed count afterCall tapeOutside,
    Listing8LateFrames.initial_image mode l t v sentinel (Listing8BootImage.beginPC mode origin) r body _ observed count afterRegion sources.1 sources.2]
  rw [Listing8FailureGlobalImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing8FailureGlobalImage.region_end]
    dsimp only [Listing8FailureLayout.callPC] at afterCall
    omega)),byte_frame _ _ _ _ _ (Or.inl afterCall)]
  rw [Listing8GlobalBoot.extra,byte_frame _ _ _ _ _ (Or.inl (by rw [Listing4EntryLayout.bytes_length];exact bootBefore)),
    Listing8JumpImage.backing,byte_frame _ _ _ _ _ (Or.inl prefixBefore)]

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel limit : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (tail : Listing8FailLayout.Bounds mode origin l limit)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GlobalJump.bodyEnd mode origin l t v sentinel (backing mode origin memory) seed).principal.memory
      (Listing8JumpLayout.failPC mode origin) (Listing4TargetLayout.size mode)=Listing8FailLayout.bytes mode origin := by
  rw [body_window mode origin l t v sentinel limit r owners copies boot body tail (backing mode origin memory) seed _ _
    (Nat.le_refl _) tail.continuation]
  simpa only [backing,Listing8FailLayout.bytes_length] using ByteMemory.bytes_at_put memory (Listing8JumpLayout.failPC mode origin) (Listing8FailLayout.bytes mode origin)
end SmcTuring.Appendix.Listing8FailImage

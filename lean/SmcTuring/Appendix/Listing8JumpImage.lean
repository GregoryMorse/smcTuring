module
public import SmcTuring.Appendix.Listing8JumpLayout

public section
namespace SmcTuring.Appendix.Listing8JumpImage
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def backing (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) :=
  ByteMemory.putBytes memory (Listing8JumpLayout.jumpPC mode origin) (Listing8JumpLayout.prefixBytes mode origin)
theorem call_position (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin)) :
    Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l sentinel)=Listing8JumpLayout.callPC mode origin := by
  rw [(Listing8BootControl.call_positions mode origin l t sentinel boot body).1,(Listing8JumpLayout.positions mode origin).1]
theorem end_position (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin)) :
    Listing8FailureLayout.endPC mode (Listing8BootControl.region mode origin l sentinel)=Listing8JumpLayout.jumpPC mode origin := by
  have coords:=call_position mode origin l t sentinel boot body
  cases mode <;> dsimp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan,
    Listing8JumpLayout.callPC,Listing4JumpLayout.prefixSize] at coords <;> omega
theorem capacity (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin)) :
    Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes) := by
  have cap:=body.capacity
  change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l sentinel)+5<_ at cap
  rw [call_position mode origin l t sentinel boot body] at cap
  exact cap

/-- The stack-prefix gap retains initialized bytes through every actual body
write; the failure operand writes lie on either side of this entire window. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GlobalBoot.finish mode origin l t v sentinel (backing mode origin memory) seed).principal.memory
      (Listing8JumpLayout.jumpPC mode origin) (Listing8JumpLayout.prefixBytes mode origin).length=Listing8JumpLayout.prefixBytes mode origin := by
  let region:=Listing8BootControl.region mode origin l sentinel
  let extra:=Listing8GlobalBoot.extra mode origin (backing mode origin memory)
  let state:=Listing8GlobalBoot.bodySeed mode origin seed
  have endEq:=end_position mode origin l t sentinel boot body
  change Listing8FailureLayout.endPC mode region=_ at endEq
  have callEq:=call_position mode origin l t sentinel boot body
  change Listing8FailureLayout.callPC mode region=_ at callEq
  have coords:=Listing8FailureLayout.positions mode region
  have after : region.start ≤ Listing8JumpLayout.jumpPC mode origin := by
    have endAfter:=coords.2.2.2.1
    rw [←endEq];omega
  have upper : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length ≤ Listing8FailureLayout.callPC mode region+5 := by
    rw [callEq,Listing8JumpLayout.prefix_length]
    dsimp [Listing8JumpLayout.callPC];omega
  have andBefore : Listing8FailureLayout.andPC mode region+10 ≤ Listing8JumpLayout.jumpPC mode origin := by
    rw [←endEq];simp only [Listing8FailureLayout.endPC,Listing8FailureLayout.xorPC];omega
  have maskBefore : Listing8FailureLayout.mask mode region+4 ≤ Listing8JumpLayout.jumpPC mode origin := by
    rw [←endEq];simp only [Listing8FailureLayout.mask,Listing8FailureLayout.endPC];omega
  have callAfter : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length ≤ Listing8FailureLayout.callPC mode region := by
    rw [callEq,Listing8JumpLayout.prefix_length];rfl
  change ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t v sentinel (Listing8BootImage.beginPC mode origin) extra state).principal.memory _ _=_
  rw [Listing8GlobalFailure.finish]
  change ByteMemory.bytesAt (Listing8FailureImage.finish mode region
    (Listing8GlobalFailure.entryState mode l t v sentinel (Listing8BootImage.beginPC mode origin) extra state)).principal.memory _ _=_
  rw [Listing8FailureValues.window mode region
    (Listing8FailureGeometry.local_bounds mode l t sentinel (Listing8BootImage.beginPC mode origin) r body) _
    (Listing8GlobalFailure.entry mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body extra state)
    (Listing8FailureGlobalImage.current_region mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body extra state)
    _ _ (Or.inl andBefore) (Or.inl maskBefore) (Or.inr (by omega))]
  rw [Listing8GlobalFailure.entryState,Listing8FailureFrames.after_state mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ state _ _ after upper]
  change ByteMemory.bytesAt (Listing8FailureGlobalImage.memory mode l t v sentinel (Listing8BootImage.beginPC mode origin) extra) _ _=_
  rw [Listing8FailureGlobalImage.image_window mode l t v sentinel (Listing8BootImage.beginPC mode origin) r body extra _ _ after upper]
  have regionLength:=Listing8FailureGlobalImage.region_end mode l sentinel (Listing8BootImage.beginPC mode origin)
  change region.start+(Listing8FailureLayout.bytes mode region).length=Listing8FailureLayout.endPC mode region at regionLength
  dsimp only [region,Listing8BootControl.region] at callAfter
  rw [Listing8FailureGlobalImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
    change region.start+(Listing8FailureLayout.bytes mode region).length ≤ _
    rw [regionLength];exact Nat.le_of_eq endEq)),
    byte_frame _ _ _ _ _ (Or.inr callAfter)]
  change ByteMemory.bytesAt (Listing8GlobalBoot.extra mode origin (backing mode origin memory)) _ _=_
  rw [Listing8GlobalBoot.extra,byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing4EntryLayout.bytes_length]
    cases mode <;> dsimp [Listing4EntryLayout.size,Listing8JumpLayout.jumpPC] <;> omega))]
  exact ByteMemory.bytes_at_put memory _ _
end SmcTuring.Appendix.Listing8JumpImage

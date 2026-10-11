module
public import SmcTuring.Appendix.Listing8GlobalJump

public section
namespace SmcTuring.Appendix.Listing8JumpValues
open Native Listing8CopyImage Listing8GlobalJump
abbrev Targets:=Listing8PointerCopies.Targets
theorem add_carry_clear (origin : Nat) (state : StringExecution.State .x64)
    (capacity : Listing8JumpLayout.failPC .x64 origin<2^64) : Listing4JumpEffects.flag .x64 origin state=false := by
  rw [(Listing8JumpLayout.positions .x64 origin).2] at capacity
  change origin+1274<2^64 at capacity
  have fieldFits : Listing4StackLayout.stptr .x64 origin<2^64 := by dsimp [Listing4StackLayout.stptr];omega
  change decide ((BitVec.ofNat 64 (Listing4StackLayout.stptr .x64 origin)).toNat+(BitVec.ofNat 64 18).toNat ≥ 2^64)=false
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fieldFits,Nat.mod_eq_of_lt (by decide : 18<2^64)]
  apply decide_eq_false
  dsimp [Listing4StackLayout.stptr];omega

theorem failure_condition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    failed mode origin l t v sentinel memory seed=
      decide ((if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next)=Arithmetic.encodeNat mode sentinel) :=
  Listing8BootControl.failure_condition mode origin l t v sentinel r owners copies body _ seed

theorem return_word (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel memory seed).principal.memory (Listing4StackLayout.returnField mode origin)=
      Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin) := by
  rw [effect mode origin l t v sentinel r owners copies boot body memory seed,MixedMemory.get_put]

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel memory seed).principal.pc=
      if decide ((if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next)=Arithmetic.encodeNat mode sentinel)
      then Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin) else Arithmetic.encodeNat mode (Listing8BootImage.beginPC mode origin) := by
  rw [effect mode origin l t v sentinel r owners copies boot body memory seed]
  rw [failure_condition mode origin l t v sentinel r owners copies body memory seed]

theorem saved_stack (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel memory seed).principal.memory (Listing4StackLayout.stptr mode origin)=seed.principal.stack := by
  rw [effect mode origin l t v sentinel r owners copies boot body memory seed,
    MixedFrames.word_after_word mode _ _ _ _ (Listing4StackLayout.fields_separate mode origin),MixedMemory.get_put]
  exact (Listing8GlobalBootValues.registers mode origin l t v sentinel r owners copies body (Listing8JumpImage.backing mode origin memory) seed).1

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel memory seed).principal.stack=Arithmetic.encodeNat mode (Listing4StackLayout.returnField mode origin) ∧
    (finish mode origin l t v sentinel memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t v sentinel memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t v sentinel memory seed).backwards=false ∧
    (finish mode origin l t v sentinel memory seed).principal.carry=false ∧
    (finish mode origin l t v sentinel memory seed).principal.accumulator=(bodyEnd mode origin l t v sentinel memory seed).principal.accumulator := by
  have prior:=Listing8GlobalBootValues.registers mode origin l t v sentinel r owners copies body (Listing8JumpImage.backing mode origin memory) seed
  have clear : Listing4JumpEffects.flag mode origin (bodyEnd mode origin l t v sentinel memory seed)=false := by
    cases mode with
    | x86 => exact prior.2.2.2.2.1
    | x64 => exact add_carry_clear origin _ (Listing8JumpImage.capacity .x64 origin l t sentinel boot body)
  rw [effect mode origin l t v sentinel r owners copies boot body memory seed]
  exact ⟨rfl,prior.2.1,prior.2.2.1,prior.2.2.2.1,clear,rfl⟩
end SmcTuring.Appendix.Listing8JumpValues

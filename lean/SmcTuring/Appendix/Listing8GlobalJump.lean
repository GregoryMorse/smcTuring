module
public import SmcTuring.Appendix.Listing8JumpImage
public import SmcTuring.Appendix.Listing8JumpTrace

public section
namespace SmcTuring.Appendix.Listing8GlobalJump
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalBoot.initial mode origin l t v sentinel (Listing8JumpImage.backing mode origin memory) seed
@[expose] def bodyEnd (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalBoot.finish mode origin l t v sentinel (Listing8JumpImage.backing mode origin memory) seed
@[expose] def failed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8BootControl.failed mode origin l t v sentinel (Listing8JumpImage.backing mode origin memory) seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8JumpEffects.finish mode origin (failed mode origin l t v sentinel memory seed) (bodyEnd mode origin l t v sentinel memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalBoot.program mode origin l t v sentinel (Listing8JumpImage.backing mode origin memory) seed++
    Listing8JumpLayout.forms mode origin (failed mode origin l t v sentinel memory seed)

theorem call_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (bodyEnd mode origin l t v sentinel memory seed).principal.memory (Listing8JumpLayout.callPC mode origin) 5=
      Native.encode mode (Listing8JumpLayout.call mode origin (failed mode origin l t v sentinel memory seed)) := by
  have packet:=Listing8FailureGlobalValues.call_packet mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body
    (Listing8GlobalBoot.extra mode origin (Listing8JumpImage.backing mode origin memory)) (Listing8GlobalBoot.bodySeed mode origin seed)
  change ByteMemory.bytesAt (bodyEnd mode origin l t v sentinel memory seed).principal.memory
    (Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l sentinel)) 5=
      Native.encode mode (.callRelative (if failed mode origin l t v sentinel memory seed then 0 else
        Relocation.relative32 (Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l sentinel)+5)
          (Listing8BootImage.beginPC mode origin))) at packet
  rw [Listing8JumpImage.call_position mode origin l t sentinel boot body] at packet
  exact packet

/-- One initialized image executes the printed bootstrap, body, failure mask,
later stack prefix and actual conditional CALL. No future packet or trace is a
premise; every intermediate value/image/fetch is derived. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (initial mode origin l t v sentinel memory seed) (program mode origin l t v sentinel memory seed)
      (finish mode origin l t v sentinel memory seed) := by
  have first:=Listing8GlobalBoot.trace mode origin l t v sentinel r owners copies boot body (Listing8JumpImage.backing mode origin memory) seed
  have last:=Listing8JumpTrace.trace mode origin (failed mode origin l t v sentinel memory seed) (bodyEnd mode origin l t v sentinel memory seed)
    (Listing8GlobalBoot.endpoint mode origin l t v sentinel r owners copies boot body (Listing8JumpImage.backing mode origin memory) seed)
    (Listing8JumpImage.capacity mode origin l t sentinel boot body)
    (Listing8StackMetadata.stack_packet mode origin l t v sentinel r owners copies boot body (Listing8JumpImage.backing mode origin memory) seed)
    (Listing8JumpImage.current mode origin l t v sentinel r owners copies boot body memory seed)
    (call_packet mode origin l t v sentinel r owners copies boot body memory seed)
  exact StringStack.trace_append mode first last

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t v sentinel memory seed).length=(if mode=.x86 then 142 else 190) := by
  rw [program,List.length_append,Listing8GlobalBoot.instruction_count,Listing8JumpLayout.instruction_count]
  cases mode <;> rfl

theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    finish mode origin l t v sentinel memory seed=
      {bodyEnd mode origin l t v sentinel memory seed with principal:={(bodyEnd mode origin l t v sentinel memory seed).principal with
      pc:=(if failed mode origin l t v sentinel memory seed then Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)
        else Arithmetic.encodeNat mode (Listing8BootImage.beginPC mode origin))
      stack:=Arithmetic.encodeNat mode (Listing4StackLayout.returnField mode origin)
      carry:=Listing4JumpEffects.flag mode origin (bodyEnd mode origin l t v sentinel memory seed)
      memory:=ByteMemory.putWord mode
        (ByteMemory.putWord mode (bodyEnd mode origin l t v sentinel memory seed).principal.memory (Listing4StackLayout.stptr mode origin)
          (bodyEnd mode origin l t v sentinel memory seed).principal.stack)
        (Listing4StackLayout.returnField mode origin) (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin))}} :=
  Listing8JumpEffects.called_effect mode origin _ _
    (Listing8GlobalBoot.endpoint mode origin l t v sentinel r owners copies boot body (Listing8JumpImage.backing mode origin memory) seed)
    (Listing8JumpImage.capacity mode origin l t sentinel boot body)
    (Listing8StackMetadata.stack_packet mode origin l t v sentinel r owners copies boot body (Listing8JumpImage.backing mode origin memory) seed)
end SmcTuring.Appendix.Listing8GlobalJump

module
public import SmcTuring.Appendix.Listing8FailImage

public section
namespace SmcTuring.Appendix.Listing8FailReturn
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalJump.initial mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed
@[expose] def failed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalJump.failed mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed
@[expose] def targetSeed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8BeginReturn.targetSeed mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing4TargetEffects.finish mode origin (Listing8JumpLayout.failPC mode origin)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin l t v sentinel memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalJump.program mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed++
    Listing4TargetLayout.forms mode origin (Listing8JumpLayout.failPC mode origin)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel limit : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (tail : Listing8FailLayout.Bounds mode origin l limit)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (isFailed : failed mode origin l t v sentinel memory seed=true) :
    StringStack.Trace mode (initial mode origin l t v sentinel memory seed) (program mode origin l t v sentinel memory seed)
      (finish mode origin l t v sentinel memory seed) := by
  have capacity:=Listing8GlobalBoot.entry_capacity mode origin l t sentinel boot body
  have shape:=Listing8BeginReturn.call_shape mode origin l t v sentinel r owners copies boot body (Listing8FailImage.backing mode origin memory) seed
  change Listing8GlobalJump.failed mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed=true at isFailed
  simp only [Listing8BeginReturn.target,isFailed,ite_true] at shape
  have last:=Listing4TargetTrace.trace mode origin (Listing8JumpLayout.failPC mode origin)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin l t v sentinel memory seed)
    (Listing8FailLayout.ranges mode origin) (Listing4EntryLayout.stack_capacity mode origin capacity)
    (Listing8FailLayout.capacity mode origin l limit tail)
    (Listing8StackMetadata.stack_packet mode origin l t v sentinel r owners copies boot body
      (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin memory)) seed)
    (Listing8FailLayout.placement mode origin)
    (Listing8FailImage.current mode origin l t v sentinel limit r owners copies boot body tail memory seed)
  rw [targetSeed] at last
  rw [←shape] at last
  exact StringStack.trace_append mode (Listing8GlobalJump.trace mode origin l t v sentinel r owners copies boot body (Listing8FailImage.backing mode origin memory) seed) last

theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    finish mode origin l t v sentinel memory seed=
      {Listing8GlobalJump.bodyEnd mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed with
      principal:={(Listing8GlobalJump.bodyEnd mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed).principal with
      pc:=Arithmetic.encodeNat mode (Listing8FailLayout.endPC mode origin)
      carry:=false}} := by
  have capacity:=Listing8GlobalBoot.entry_capacity mode origin l t sentinel boot body
  rw [finish,Listing4TargetEffects.effect mode origin (Listing8JumpLayout.failPC mode origin)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin l t v sentinel memory seed)
    (Listing8FailLayout.ranges mode origin) (Listing4EntryLayout.stack_capacity mode origin capacity)
    (Listing8StackMetadata.stack_packet mode origin l t v sentinel r owners copies boot body
      (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin memory)) seed)]
  rw [(Listing4TargetLayout.positions mode (Listing8JumpLayout.failPC mode origin)).2.2.2,
    Listing4EntryValues.target_carry_clear mode origin capacity]
  rfl

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t v sentinel memory seed).length=(if mode=.x86 then 147 else 195) := by
  rw [program,List.length_append,Listing8GlobalJump.instruction_count,Listing4TargetLayout.instruction_count]
  cases mode <;> rfl

theorem later_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel limit : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (tail : Listing8FailLayout.Bounds mode origin l limit)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat)
    (after : Listing8FailLayout.endPC mode origin ≤ observed) (upper : observed+count ≤ limit) :
    ByteMemory.bytesAt (finish mode origin l t v sentinel memory seed).principal.memory observed count=ByteMemory.bytesAt memory observed count := by
  have failBefore : Listing8JumpLayout.failPC mode origin ≤ observed := by
    dsimp [Listing8FailLayout.endPC] at after;omega
  rw [effect mode origin l t v sentinel r owners copies boot body memory seed,
    Listing8FailImage.body_window mode origin l t v sentinel limit r owners copies boot body tail (Listing8FailImage.backing mode origin memory) seed observed count failBefore upper,
    Listing8FailImage.backing,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by
      rw [Listing8FailLayout.bytes_length];exact after))]
end SmcTuring.Appendix.Listing8FailReturn

module
public import SmcTuring.Appendix.Listing8GraphNextStackImage

public section
namespace SmcTuring.Appendix.Listing8GraphNextJump
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8JumpEffects.finish mode origin (Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed)
    (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextFailure.program mode origin l t g node rule target memory seed++
    Listing8JumpLayout.forms mode origin (Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed)

theorem entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin) := by
  rw [Listing8GraphNextFailure.endpoint mode origin l t g node rule target ctx selected memory seed]
  exact congrArg (Arithmetic.encodeNat mode) (Listing8JumpImage.end_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)

theorem call_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory (Listing8JumpLayout.callPC mode origin) 5=
      Native.encode mode (Listing8JumpLayout.call mode origin (Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed)) := by
  have packet:=Listing8GraphNextCallImage.call_packet mode origin l t g node rule target ctx selected memory seed
  unfold Listing8FailureLayout.original at packet
  have position:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.callPC mode origin at position
  rw [position] at packet
  exact packet

theorem jump_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed)
      (Listing8JumpLayout.forms mode origin (Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed))
      (finish mode origin l t g node rule target memory seed) :=
  Listing8JumpTrace.trace mode origin _ _ (entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
    (Listing8GraphNextStackImage.stack_packet mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextStackImage.jump_prefix mode origin l t g node rule target ctx selected memory seed)
    (call_packet mode origin l t g node rule target ctx selected memory seed)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextFailure.trace mode origin l t g node rule target ctx selected memory seed)
    (jump_trace mode origin l t g node rule target ctx selected memory seed)

theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let state:=Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed
    finish mode origin l t g node rule target memory seed={state with principal:={state.principal with
      pc:=(if Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed then Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin) else Arithmetic.encodeNat mode (Listing8BootImage.beginPC mode origin))
      stack:=Arithmetic.encodeNat mode (Listing4StackLayout.returnField mode origin)
      carry:=Listing4JumpEffects.flag mode origin state
      memory:=ByteMemory.putWord mode (ByteMemory.putWord mode state.principal.memory (Listing4StackLayout.stptr mode origin) state.principal.stack)
        (Listing4StackLayout.returnField mode origin) (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin))}} :=
  Listing8JumpEffects.called_effect mode origin _ _ (entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
    (Listing8GraphNextStackImage.stack_packet mode origin l t g node rule target ctx selected memory seed)

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 281 else 372) := by
  rw [program,List.length_append,Listing8GraphNextFailure.instruction_count,Listing8JumpLayout.instruction_count]
  cases mode <;> rfl

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.stack=Arithmetic.encodeNat mode (Listing4StackLayout.returnField mode origin) ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule target memory seed).principal.accumulator=(Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.accumulator := by
  have prior:=Listing8GraphNextFailure.registers mode origin l t g node rule target ctx selected memory seed
  have clear : Listing4JumpEffects.flag mode origin (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed)=false := by
    cases mode with
    | x86 => exact prior.2.2.2.2.1
    | x64 => exact Listing8JumpValues.add_carry_clear origin _ (Listing8JumpImage.capacity .x64 origin l t _ ctx.boot ctx.body)
  rw [effect mode origin l t g node rule target ctx selected memory seed]
  exact ⟨rfl,prior.2.1,prior.2.2.1,prior.2.2.2.1,clear,rfl⟩

theorem saved_stack (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory (Listing4StackLayout.stptr mode origin)=seed.principal.stack := by
  rw [effect mode origin l t g node rule target ctx selected memory seed,
    MixedFrames.word_after_word mode _ _ _ _ (Listing4StackLayout.fields_separate mode origin),MixedMemory.get_put]
  exact (Listing8GraphNextFailure.registers mode origin l t g node rule target ctx selected memory seed).1

theorem return_field (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory (Listing4StackLayout.returnField mode origin)=Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin) := by
  rw [effect mode origin l t g node rule target ctx selected memory seed,MixedMemory.get_put]

end SmcTuring.Appendix.Listing8GraphNextJump

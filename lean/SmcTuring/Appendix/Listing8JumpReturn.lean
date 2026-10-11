module
public import SmcTuring.Appendix.Listing8FailLayout

public section
namespace SmcTuring.Appendix.Listing8JumpReturn
open Native
@[expose] def target (mode : Mode) (origin : Nat) (failed : Bool) :=
  if failed then Listing8JumpLayout.failPC mode origin else Listing8BootImage.beginPC mode origin
@[expose] def targetSeed (mode : Mode) (origin : Nat) (state : StringExecution.State mode) :=
  {state with principal:={state.principal with carry:=Listing4JumpEffects.flag mode origin state}}
@[expose] def finish (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode) :=
  Listing4TargetEffects.finish mode origin (target mode origin failed)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin state)
@[expose] def program (mode : Mode) (origin : Nat) (failed : Bool) :=
  Listing8JumpLayout.forms mode origin failed++Listing4TargetLayout.forms mode origin (target mode origin failed)

/-- These are present packets in the same memory at stack-prefix entry.
The actual CALL and target trace, including all intervening writes, are derived. -/
structure Current (mode : Mode) (origin : Nat) (failed : Bool) (memory : ByteMemory.Memory) : Prop where
  stackImage : ByteMemory.bytesAt memory origin (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode origin
  prefixImage : ByteMemory.bytesAt memory (Listing8JumpLayout.jumpPC mode origin) (Listing8JumpLayout.prefixBytes mode origin).length=Listing8JumpLayout.prefixBytes mode origin
  callImage : ByteMemory.bytesAt memory (Listing8JumpLayout.callPC mode origin) 5=Native.encode mode (Listing8JumpLayout.call mode origin failed)
  targetImage : ByteMemory.bytesAt memory (target mode origin failed) (Listing4TargetLayout.size mode)=Listing4TargetLayout.bytes mode origin (target mode origin failed)

theorem ranges (mode : Mode) (origin : Nat) (failed : Bool) :
    Listing4TargetLayout.Ranges mode origin (target mode origin failed) := by
  cases failed
  · exact Listing4EntryLayout.begin_ranges mode origin
  · exact Listing8FailLayout.ranges mode origin

theorem placement (mode : Mode) (origin : Nat) (failed : Bool) :
    origin+Listing4StackLayout.size mode≤target mode origin failed := by
  cases failed
  · exact Listing4EntryLayout.target_after_stack mode origin
  · exact Listing8FailLayout.placement mode origin

theorem call_shape (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (current : Current mode origin failed state.principal.memory) :
    Listing8JumpEffects.finish mode origin failed state=
      Listing4TargetEffects.entry mode origin (target mode origin failed)
        (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin state) := by
  rw [Listing8JumpEffects.called_effect mode origin failed state entry capacity current.stackImage,
    Listing4TargetEffects.entry,targetSeed]
  rw [MixedFrames.words_commute mode state.principal.memory (Listing4StackLayout.stptr mode origin)
    (Listing4StackLayout.returnField mode origin) _ _ (Or.symm (Listing4StackLayout.fields_separate mode origin))]
  cases failed <;> rfl

theorem trace (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (targetFits : target mode origin failed+Listing4TargetLayout.size mode<2^(8*mode.wordBytes))
    (current : Current mode origin failed state.principal.memory) :
    StringStack.Trace mode state (program mode origin failed) (finish mode origin failed state) := by
  have first:=Listing8JumpTrace.trace mode origin failed state entry capacity current.stackImage current.prefixImage current.callImage
  have last:=Listing4TargetTrace.trace mode origin (target mode origin failed)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin state)
    (ranges mode origin failed) (Listing8JumpLayout.stack_capacity mode origin capacity) targetFits current.stackImage
    (placement mode origin failed) current.targetImage
  rw [←call_shape mode origin failed state entry capacity current] at last
  exact StringStack.trace_append mode first last

theorem effect (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (current : Current mode origin failed state.principal.memory) :
    finish mode origin failed state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (Listing4TargetLayout.endPC mode (target mode origin failed))
      carry:=Listing4TargetEffects.flag mode origin}} := by
  rw [finish,Listing4TargetEffects.effect mode origin (target mode origin failed)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin state)
    (ranges mode origin failed) (Listing8JumpLayout.stack_capacity mode origin capacity) current.stackImage]
  rfl

theorem instruction_count (mode : Mode) (origin : Nat) (failed : Bool) :
    (program mode origin failed).length=(if mode=.x86 then 7 else 9) := by
  rw [program,List.length_append,Listing8JumpLayout.instruction_count,Listing4TargetLayout.instruction_count]
  cases mode <;> rfl

theorem current_after (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (current : Current mode origin failed state.principal.memory) :
    Current mode origin failed (finish mode origin failed state).principal.memory := by
  rw [effect mode origin failed state capacity current]
  exact current

end SmcTuring.Appendix.Listing8JumpReturn

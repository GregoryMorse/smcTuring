module
public import SmcTuring.Appendix.Listing8GlobalJump
public import SmcTuring.Appendix.Listing4EntryValues

public section
namespace SmcTuring.Appendix.Listing8BeginReturn
open Native Listing8CopyImage Listing8GlobalJump
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def target (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  if failed mode origin l t v sentinel memory seed then Listing8JumpLayout.failPC mode origin else Listing8BootImage.beginPC mode origin
@[expose] def targetSeed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  let state:=bodyEnd mode origin l t v sentinel memory seed
  {state with principal:={state.principal with carry:=Listing4JumpEffects.flag mode origin state}}
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing4TargetEffects.finish mode origin (Listing8BootImage.beginPC mode origin)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin l t v sentinel memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalJump.program mode origin l t v sentinel memory seed++Listing4TargetLayout.forms mode origin (Listing8BootImage.beginPC mode origin)

theorem call_shape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GlobalJump.finish mode origin l t v sentinel memory seed=
      Listing4TargetEffects.entry mode origin (target mode origin l t v sentinel memory seed)
        (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin l t v sentinel memory seed) := by
  rw [Listing8GlobalJump.effect mode origin l t v sentinel r owners copies boot body memory seed,
    Listing4TargetEffects.entry,targetSeed]
  rw [MixedFrames.words_commute mode (bodyEnd mode origin l t v sentinel memory seed).principal.memory
    (Listing4StackLayout.stptr mode origin) (Listing4StackLayout.returnField mode origin) _ _
    (Or.symm (Listing4StackLayout.fields_separate mode origin))]
  cases h : failed mode origin l t v sentinel memory seed <;> simp only [target,h,Bool.false_eq_true,ite_false,ite_true]

theorem target_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (targetSeed mode origin l t v sentinel memory seed).principal.memory
      (Listing8BootImage.beginPC mode origin) (Listing4TargetLayout.size mode)=
        Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin) := by
  have current:=Listing8StackMetadata.code_current mode origin l t v sentinel r owners copies boot body (Listing8JumpImage.backing mode origin memory) seed
  have packet:=ByteWindow.packet (bodyEnd mode origin l t v sentinel memory seed).principal.memory origin
    (Listing4Boot.bytes mode origin) (Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin)) [] (by
      simp only [List.append_nil]
      change ByteMemory.bytesAt _ origin (Listing4EntryLayout.bytes mode origin).length=Listing4EntryLayout.bytes mode origin
      rw [Listing4EntryLayout.bytes_length];exact current)
  have typed : ByteMemory.bytesAt (bodyEnd mode origin l t v sentinel memory seed).principal.memory (origin+Listing4Boot.size mode)
      (Listing4TargetLayout.size mode)=Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin) := by
    simpa only [Listing4Boot.bytes_length,Listing4TargetLayout.bytes_length] using packet
  rw [←Listing4Boot.endpoint] at typed
  exact typed

/-- On the computed nonfailure branch, the actual CALL result executes all
five begin packets and returns to main with the whole post-body memory intact. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (notFailed : failed mode origin l t v sentinel memory seed=false) :
    StringStack.Trace mode (initial mode origin l t v sentinel memory seed) (program mode origin l t v sentinel memory seed)
      (finish mode origin l t v sentinel memory seed) := by
  have capacity:=Listing8GlobalBoot.entry_capacity mode origin l t sentinel boot body
  have shape:=call_shape mode origin l t v sentinel r owners copies boot body memory seed
  simp only [target,notFailed,Bool.false_eq_true,ite_false] at shape
  have last:=Listing4TargetTrace.trace mode origin (Listing8BootImage.beginPC mode origin)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin l t v sentinel memory seed)
    (Listing4EntryLayout.begin_ranges mode origin) (Listing4EntryLayout.stack_capacity mode origin capacity)
    (Listing4EntryLayout.target_capacity mode origin capacity)
    (Listing8StackMetadata.stack_packet mode origin l t v sentinel r owners copies boot body (Listing8JumpImage.backing mode origin memory) seed)
    (Listing4EntryLayout.target_after_stack mode origin)
    (target_current mode origin l t v sentinel r owners copies boot body memory seed)
  rw [←shape] at last
  exact StringStack.trace_append mode (Listing8GlobalJump.trace mode origin l t v sentinel r owners copies boot body memory seed) last

theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    finish mode origin l t v sentinel memory seed=
      {bodyEnd mode origin l t v sentinel memory seed with principal:={(bodyEnd mode origin l t v sentinel memory seed).principal with
      pc:=Arithmetic.encodeNat mode l.start
      carry:=false}} := by
  have capacity:=Listing8GlobalBoot.entry_capacity mode origin l t sentinel boot body
  rw [finish,Listing4TargetEffects.effect mode origin (Listing8BootImage.beginPC mode origin)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)) (targetSeed mode origin l t v sentinel memory seed)
    (Listing4EntryLayout.begin_ranges mode origin) (Listing4EntryLayout.stack_capacity mode origin capacity)
    (Listing8StackMetadata.stack_packet mode origin l t v sentinel r owners copies boot body (Listing8JumpImage.backing mode origin memory) seed)]
  have endpoint:=Listing4EntryLayout.endpoint mode origin
  change Listing4TargetLayout.endPC mode (Listing8BootImage.beginPC mode origin)=Listing4EntryLayout.mainPC mode origin at endpoint
  rw [endpoint,←boot.packed,Listing4EntryValues.target_carry_clear mode origin capacity]
  rfl

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t v sentinel memory seed).length=(if mode=.x86 then 147 else 195) := by
  rw [program,List.length_append,Listing8GlobalJump.instruction_count,Listing4TargetLayout.instruction_count]
  cases mode <;> rfl
end SmcTuring.Appendix.Listing8BeginReturn

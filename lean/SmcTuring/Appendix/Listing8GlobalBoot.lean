module
public import SmcTuring.Appendix.Listing8BootImage

public section
namespace SmcTuring.Appendix.Listing8GlobalBoot
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def extra (mode : Mode) (origin : Nat) (backing : ByteMemory.Memory) :=
  ByteMemory.putBytes backing origin (Listing4EntryLayout.bytes mode origin)
@[expose] def bootSeed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  {seed with
    principal := {seed.principal with
    memory := Listing8FailureGlobalImage.memory mode l t v sentinel (Listing8BootImage.beginPC mode origin) backing}
    backwards := false}
@[expose] def initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing4Entry.initial mode origin (bootSeed mode origin l t v sentinel backing seed)
@[expose] def bodySeed (mode : Mode) (origin : Nat) (seed : StringExecution.State mode) :=
  {seed with
    principal := {seed.principal with
    accumulator := Listing4StackInit.accumulator mode origin seed
    carry := Listing4TargetEffects.flag mode origin}
    backwards := false}
@[expose] def bodyInitial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  let base := bodySeed mode origin seed
  {base with
    principal := {base.principal with
    pc := Arithmetic.encodeNat mode l.start
    memory := Listing8FailureGlobalImage.memory mode l t v sentinel (Listing8BootImage.beginPC mode origin) (extra mode origin backing)}
    backwards := false}
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalFailure.finish mode l t v sentinel (Listing8BootImage.beginPC mode origin) (extra mode origin backing) (bodySeed mode origin seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing4EntryLayout.forms mode origin++
    (Listing8GlobalFailure.program mode l t v sentinel (Listing8BootImage.beginPC mode origin) (extra mode origin backing) (bodySeed mode origin seed)).map StringStack.Form.previous

theorem entry_capacity (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin)) :
    Listing4EntryLayout.mainPC mode origin<2^(8*mode.wordBytes) := by
  rw [←boot.packed]
  have coords := Listing8FailureGeometry.positions mode l t sentinel (Listing8BootImage.beginPC mode origin) body
  have cap:=body.capacity
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega

/-- The complete executed bootstrap result equals the initialized body state.
This bridge follows from native execution, operand restoration and disjoint
initial overlays; no state/image equality is taken as a premise. -/
theorem body_entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing4Entry.finish mode origin (bootSeed mode origin l t v sentinel backing seed)=
      bodyInitial mode origin l t v sentinel backing seed := by
  have actual := Listing4Entry.effect mode origin (bootSeed mode origin l t v sentinel backing seed) (entry_capacity mode origin l t sentinel boot body)
  have memory := Listing8BootImage.memory_put mode origin l t v sentinel (Listing8BootImage.beginPC mode origin) r boot body backing
  have acc : Listing4StackInit.accumulator mode origin
      (Listing4Entry.initial mode origin (bootSeed mode origin l t v sentinel backing seed))=
      Listing4StackInit.accumulator mode origin seed := by cases mode <;> rfl
  rw [actual]
  simp only [Listing4Entry.targetSeed,acc]
  change {seed with
    principal := {seed.principal with
    pc := Arithmetic.encodeNat mode (Listing4EntryLayout.mainPC mode origin)
    accumulator := Listing4StackInit.accumulator mode origin seed
    carry := Listing4TargetEffects.flag mode origin
    memory := ByteMemory.putBytes (Listing8FailureGlobalImage.memory mode l t v sentinel (Listing8BootImage.beginPC mode origin) backing)
      origin (Listing4EntryLayout.bytes mode origin)}
    backwards := false}=
    {seed with
    principal := {seed.principal with
    pc := Arithmetic.encodeNat mode l.start
    accumulator := Listing4StackInit.accumulator mode origin seed
    carry := Listing4TargetEffects.flag mode origin
    memory := Listing8FailureGlobalImage.memory mode l t v sentinel (Listing8BootImage.beginPC mode origin) (extra mode origin backing)}
    backwards := false}
  rw [←memory,boot.packed]
  rfl

/-- Full printed entry and every existing actual Listing 8 instruction through
failure-mask/CALL-operand selection execute from one constructed initial image. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (initial mode origin l t v sentinel backing seed) (program mode origin l t v sentinel backing seed)
      (finish mode origin l t v sentinel backing seed) := by
  have first := Listing4Entry.trace mode origin (bootSeed mode origin l t v sentinel backing seed) (entry_capacity mode origin l t sentinel boot body)
  have last := StringStack.previous_trace mode (Listing8GlobalFailure.trace mode l t v sentinel (Listing8BootImage.beginPC mode origin)
    r owners copies body (extra mode origin backing) (bodySeed mode origin seed))
  change StringStack.Trace mode (bodyInitial mode origin l t v sentinel backing seed)
    ((Listing8GlobalFailure.program mode l t v sentinel (Listing8BootImage.beginPC mode origin) (extra mode origin backing) (bodySeed mode origin seed)).map StringStack.Form.previous)
    (finish mode origin l t v sentinel backing seed) at last
  rw [←body_entry mode origin l t v sentinel r boot body backing seed] at last
  exact StringStack.trace_append mode first last

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t v sentinel backing seed).length=(if mode=.x86 then 140 else 186) := by
  rw [program,List.length_append,List.length_map,Listing4EntryLayout.instruction_count,Listing8GlobalFailure.instruction_count]
  cases mode <;> rfl
theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel backing seed).principal.pc=Arithmetic.encodeNat mode (origin+(if mode=.x86 then 795 else 1247)) := by
  rw [finish,Listing8GlobalFailure.endpoint mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body,
    boot.packed]
  cases mode <;> rfl
end SmcTuring.Appendix.Listing8GlobalBoot

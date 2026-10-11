module
public import SmcTuring.Appendix.Listing8GraphNextHelperImage

public section
namespace SmcTuring.Appendix.Listing8GraphNextPointers
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8PointerCopies.finish mode (nextLayout mode origin l g node rule target) t
    (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextOwners.program mode origin l t g node rule target memory seed++
    ((Listing8PointerCopies.program mode (nextLayout mode origin l g node rule target) t).map StringControl.Form.previous).map StringStack.Form.previous

theorem helper_bytes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) :
    Listing8PointerCopies.bytes mode (nextLayout mode origin l g node rule target) t=Listing8PointerCopies.bytes mode l t := rfl

theorem pointer_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed)
      (Listing8PointerCopies.program mode (nextLayout mode origin l g node rule target) t) (finish mode origin l t g node rule target memory seed) := by
  apply Listing8PointerCopies.trace mode _ t (Listing8GraphNextOwnerBounds.pointer_copies mode origin l t g node rule target ctx) _
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1
  rw [helper_bytes]
  exact Listing8GraphNextHelperImage.current mode origin l t g node rule target ctx selected memory seed
/-- All four next-pass pointer-copy calls execute after the actual copied
owners, retaining the single mutated memory throughout both body prefixes. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextOwners.trace mode origin l t g node rule target ctx selected memory seed)
    (StringStack.previous_trace mode (StringControl.previous_trace mode (pointer_trace mode origin l t g node rule target ctx selected memory seed)))
theorem entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode l.input.start := by
  have actual:=Listing8PointerCopies.endpoint mode (nextLayout mode origin l g node rule target) t
    (Listing8GraphNextOwnerBounds.pointer_copies mode origin l t g node rule target ctx) _
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1
  change (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (Listing8PointerCopies.endPC mode l) at actual
  rw [←ctx.body.state.head.input.joined] at actual
  exact actual
theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule target memory seed).principal.accumulator=
      DwordCode.lift mode (DwordCode.low mode (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.accumulator) := by
  have prior:=Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed
  have actual:=Listing8PointerCopies.registers mode _ t (Listing8GraphNextOwnerBounds.pointer_copies mode origin l t g node rule target ctx) _ prior.1
  exact ⟨actual.1.trans prior.2.1,actual.2.2.2.1.trans prior.2.2.1,actual.2.2.2.2.1.trans prior.2.2.2.1,
    actual.2.2.2.2.2.trans prior.2.2.2.2.1,actual.2.1.trans prior.2.2.2.2.2,actual.2.2.1⟩
theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 228 else 287) := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphNextOwners.instruction_count,(Listing8PointerCopies.sizes mode _ t).2.2]
  cases mode <;> rfl
theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=origin+(if mode=.x86 then 419 else 647) := by
  have small : l.input.start<2^(8*mode.wordBytes) := by
    have capacity:=ctx.resources.inputFits
    have geometry:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at geometry <;> omega
  rw [entry mode origin l t g node rule target ctx selected memory seed,Arithmetic.encode_nat_toNat mode _ small]
  have geometry:=(Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined).1
  rw [ctx.boot.packed] at geometry
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,Listing4EntryLayout.mainPC,Listing4EntryLayout.size] at geometry ⊢ <;> omega

end SmcTuring.Appendix.Listing8GraphNextPointers

module
public import SmcTuring.Appendix.Listing8GraphNextFailureImage

public section
namespace SmcTuring.Appendix.Listing8GraphNextFailure
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) := Listing8FailureImage.finish mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8GraphNextState.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextState.program mode origin l t g node rule target memory seed++(Listing8FailureTrace.program mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8GraphNextState.finish mode origin l t g node rule target memory seed)).map StringStack.Form.previous
@[expose] def failed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) := Listing8FailureValues.failed mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory

theorem failure_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringControl.Trace mode (Listing8GraphNextState.finish mode origin l t g node rule target memory seed) (Listing8FailureTrace.program mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8GraphNextState.finish mode origin l t g node rule target memory seed)) (finish mode origin l t g node rule target memory seed) :=
  Listing8FailureReuseEffects.trace mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed) (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextState.trace mode origin l t g node rule target ctx selected memory seed) (StringStack.previous_trace mode (failure_trace mode origin l t g node rule target ctx selected memory seed))

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (Listing8FailureLayout.endPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) :=
  Listing8FailureReuseEffects.endpoint mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed) (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 279 else 368) := by
  rw [program,List.length_append,List.length_map,Listing8GraphNextState.instruction_count,Listing8FailureTrace.instruction_count]
  cases mode <;> rfl

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule target memory seed).principal.accumulator=StringInit.accumulator mode (nodePC mode origin g g.halt)
      (Listing8FailureImage.resetState mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8GraphNextState.finish mode origin l t g node rule target memory seed)) := by
  have actual:=Listing8FailureReuseEffects.registers mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed) (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)
  have prior:=Listing8GraphNextState.registers mode origin l t g node rule target ctx selected memory seed
  exact ⟨actual.1.trans prior.1,actual.2.1.trans prior.2.1,actual.2.2.1.trans prior.2.2.1,
    actual.2.2.2.1.trans prior.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2⟩

theorem endpoint_offset (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=origin+(if mode=.x86 then 795 else 1247) := by
  have cap:=ctx.body.capacity
  have endBefore : Listing8FailureLayout.endPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5 := by
    unfold Listing8FailureLayout.callPC;omega
  rw [endpoint mode origin l t g node rule target ctx selected memory seed,Arithmetic.encode_nat_toNat mode _ (Nat.lt_of_le_of_lt endBefore cap),
    (Listing8FailureGeometry.positions mode l t _ _ ctx.body).2.1,ctx.boot.packed]
  cases mode <;> rfl

theorem failed_iff (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    failed mode origin l t g node rule target memory seed=true ↔ Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target := by
  unfold failed Listing8FailureValues.failed
  change decide (MixedMemory.getWord mode (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory
    (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode (nodePC mode origin g g.halt))=true ↔ _
  rw [Listing8GraphNextStateValues.logical_transition mode origin l t g node rule target ctx selected memory seed]
  simp only [decide_eq_true_eq]
  exact (Listing8GraphLabels.state_halt_iff mode origin g _ ctx.native).trans
    (Listing8GraphStep.halted_iff (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)

theorem memory_effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.memory=
      DwordCode.put (DwordCode.put (DwordCode.put (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory (Listing8FailureLayout.andPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+6) (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))))
        (Listing8FailureLayout.mask mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) &&& InputUpdate.mask (failed mode origin l t g node rule target memory seed)))
        (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+1)
        (DwordCode.get (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+1) ^^^
          (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) &&& InputUpdate.mask (failed mode origin l t g node rule target memory seed))) :=
  Listing8FailureReuseEffects.memory mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed) (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)

end SmcTuring.Appendix.Listing8GraphNextFailure

module
public import SmcTuring.Appendix.Listing8GraphNextResetControl

public section
namespace SmcTuring.Appendix.Listing8GraphNextControl
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  if Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed then
    Listing8GraphNextReset.finish mode origin l t g node rule target memory seed
  else Listing8GraphNextBegin.finish mode origin l t g node rule target memory seed
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  if Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed then
    Listing8GraphNextReset.program mode origin l t g node rule target memory seed
  else Listing8GraphNextBegin.program mode origin l t g node rule target memory seed

theorem nonhalt (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (branch : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed=false) :
    ¬Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target := by
  intro halted
  have impossible:=(Listing8GraphNextFailure.failed_iff mode origin l t g node rule target ctx selected memory seed).mpr halted
  rw [branch] at impossible
  cases impossible

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) := by
  cases branch : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed
  · simpa only [program,finish,branch,Bool.false_eq_true,ite_false] using
      Listing8GraphNextBegin.trace mode origin l t g node rule target ctx selected memory seed
        (nonhalt mode origin l t g node rule target ctx selected memory seed branch)
  · simpa only [program,finish,branch,ite_true] using
      Listing8GraphNextReset.trace mode origin l t g node rule target ctx selected memory seed
        ((Listing8GraphNextFailure.failed_iff mode origin l t g node rule target ctx selected memory seed).mp branch)

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=
      if Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed then
        (if mode=.x86 then 295 else 389)+11*g.transitions else (if mode=.x86 then 286 else 377) := by
  cases branch : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed <;>
    simp only [program,branch,Bool.false_eq_true,ite_false,ite_true,Listing8GraphNextReset.instruction_count,Listing8GraphNextBegin.instruction_count]

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=
      if Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed then Listing8GraphLayout.input mode origin g.transitions else l.start := by
  cases branch : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed
  · simp only [finish,branch,Bool.false_eq_true,ite_false]
    have capacity : l.start<2^(8*mode.wordBytes) := by
      rw [ctx.boot.packed];exact Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body
    rw [(Listing8GraphNextBegin.registers mode origin l t g node rule target ctx selected memory seed
      (nonhalt mode origin l t g node rule target ctx selected memory seed branch)).1,Arithmetic.encode_nat_toNat mode _ capacity]
  · simpa only [finish,branch,ite_true] using Listing8GraphNextReset.endpoint mode origin l t g node rule target ctx selected memory seed
      ((Listing8GraphNextFailure.failed_iff mode origin l t g node rule target ctx selected memory seed).mp branch)

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false := by
  cases branch : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed
  · simp only [finish,branch,Bool.false_eq_true,ite_false]
    have actual:=Listing8GraphNextBegin.registers mode origin l t g node rule target ctx selected memory seed
      (nonhalt mode origin l t g node rule target ctx selected memory seed branch)
    exact ⟨actual.2.1,actual.2.2.2.2.2.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.1⟩
  · simpa only [finish,branch,ite_true] using Listing8GraphNextReset.registers mode origin l t g node rule target ctx selected memory seed
      ((Listing8GraphNextFailure.failed_iff mode origin l t g node rule target ctx selected memory seed).mp branch)

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphNextInputNodes.graph g node rule target))
      (finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (finish mode origin l t g node rule target memory seed).principal.memory := by
  cases branch : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed
  · simpa only [finish,branch,Bool.false_eq_true,ite_false] using Listing8GraphNextBegin.source_graph mode origin l t g node rule target ctx selected memory seed
      (nonhalt mode origin l t g node rule target ctx selected memory seed branch)
  · simpa only [finish,branch,ite_true] using Listing8GraphNextResetOutput.source_graph mode origin l t g node rule target ctx selected memory seed
      ((Listing8GraphNextFailure.failed_iff mode origin l t g node rule target ctx selected memory seed).mp branch)

theorem control_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8JumpReturn.Current mode origin false (finish mode origin l t g node rule target memory seed).principal.memory := by
  cases branch : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed
  · simpa only [finish,branch,Bool.false_eq_true,ite_false] using Listing8GraphNextBegin.control_current mode origin l t g node rule target ctx selected memory seed
      (nonhalt mode origin l t g node rule target ctx selected memory seed branch)
  · simpa only [finish,branch,ite_true] using Listing8GraphNextResetControl.current mode origin l t g node rule target ctx selected memory seed
      ((Listing8GraphNextFailure.failed_iff mode origin l t g node rule target ctx selected memory seed).mp branch)

theorem head_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (if Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed then nodePC mode origin g g.halt else
        nodePC mode origin g (Listing8GraphStep.nextNode (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) := by
  cases branch : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed
  · simpa only [finish,branch,Bool.false_eq_true,ite_false] using Listing8GraphNextBegin.head mode origin l t g node rule target ctx selected memory seed
      (nonhalt mode origin l t g node rule target ctx selected memory seed branch)
  · simpa only [finish,branch,ite_true] using Listing8GraphNextReset.input_cursor mode origin l t g node rule target ctx selected memory seed
      ((Listing8GraphNextFailure.failed_iff mode origin l t g node rule target ctx selected memory seed).mp branch)

theorem transition_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (if Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed then Listing8FullTableImage.start mode origin else
        statePC mode origin g (Listing8GraphStep.nextRule (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) := by
  cases branch : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed
  · simpa only [finish,branch,Bool.false_eq_true,ite_false] using Listing8GraphNextBegin.transition mode origin l t g node rule target ctx selected memory seed
      (nonhalt mode origin l t g node rule target ctx selected memory seed branch)
  · simpa only [finish,branch,ite_true] using Listing8GraphNextReset.transition_cursor mode origin l t g node rule target ctx selected memory seed
      ((Listing8GraphNextFailure.failed_iff mode origin l t g node rule target ctx selected memory seed).mp branch)

end SmcTuring.Appendix.Listing8GraphNextControl

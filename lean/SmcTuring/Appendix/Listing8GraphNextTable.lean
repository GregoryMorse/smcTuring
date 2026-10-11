module
public import SmcTuring.Appendix.Listing8GraphNextFailReturn

public section
namespace SmcTuring.Appendix.Listing8GraphNextTable
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8TableTrace.finish mode (Listing8FullTableImage.start mode origin) (table mode origin g)
    (Listing8GraphNextFailReturn.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextFailReturn.program mode origin l t g node rule target memory seed++
    ((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map StringControl.Form.previous).map StringStack.Form.previous

theorem table_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    StringDword.Trace mode (Listing8GraphNextFailReturn.finish mode origin l t g node rule target memory seed)
      (Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g))
      (finish mode origin l t g node rule target memory seed) :=
  Listing8TableTrace.trace mode _ _ (Listing8GraphTableBounds.declarations_valid mode origin g ctx.native) _
    (Listing8GraphNextFailReturn.registers mode origin l t g node rule target ctx selected memory seed halted).1
    (Listing8GraphNextFailReturn.source_graph mode origin l t g node rule target ctx selected memory seed halted).2

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextFailReturn.trace mode origin l t g node rule target ctx selected memory seed halted)
    (StringStack.previous_trace mode (StringControl.previous_trace mode (table_trace mode origin l t g node rule target ctx selected memory seed halted)))

theorem result (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    let prior:=Listing8GraphNextFailReturn.finish mode origin l t g node rule target memory seed
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)) ∧
    (finish mode origin l t g node rule target memory seed).principal.memory=prior.principal.memory ∧
    (finish mode origin l t g node rule target memory seed).principal.stack=prior.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=prior.principal.carry ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=prior.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=prior.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=prior.backwards :=
  Listing8TableTrace.result mode _ _ (Listing8GraphTableBounds.declarations_valid mode origin g ctx.native) _
    (Listing8GraphNextFailReturn.registers mode origin l t g node rule target ctx selected memory seed halted).1
    (Listing8GraphNextFailReturn.source_graph mode origin l t g node rule target ctx selected memory seed halted).2

theorem memory_effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    (finish mode origin l t g node rule target memory seed).principal.memory=(Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory := by
  rw [(result mode origin l t g node rule target ctx selected memory seed halted).2.1,
    Listing8GraphNextFailReturn.effect mode origin l t g node rule target ctx selected memory seed halted]

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 286 else 377)+11*g.transitions := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphNextFailReturn.instruction_count,
    Listing8TableTrace.instruction_count,table_length]

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)).start :=
  (result mode origin l t g node rule target ctx selected memory seed halted).1

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false := by
  have actual:=result mode origin l t g node rule target ctx selected memory seed halted
  have prior:=Listing8GraphNextFailReturn.registers mode origin l t g node rule target ctx selected memory seed halted
  exact ⟨actual.2.2.1.trans prior.2.1,actual.2.2.2.1.trans prior.2.2.2.2.2.1,
    actual.2.2.2.2.1.trans prior.2.2.1,actual.2.2.2.2.2.1.trans prior.2.2.2.1,
    actual.2.2.2.2.2.2.trans prior.2.2.2.2.1⟩

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphNextInputNodes.graph g node rule target))
      (finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (finish mode origin l t g node rule target memory seed).principal.memory := by
  rw [memory_effect mode origin l t g node rule target ctx selected memory seed halted]
  exact Listing8GraphNextFailureFrames.source_graph mode origin l t g node rule target ctx selected memory seed

theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) := by
  rw [memory_effect mode origin l t g node rule target ctx selected memory seed halted]
  exact Listing8GraphNextFailureFrames.head mode origin l t g node rule target ctx selected memory seed

end SmcTuring.Appendix.Listing8GraphNextTable

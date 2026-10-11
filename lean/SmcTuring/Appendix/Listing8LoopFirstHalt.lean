module
public import SmcTuring.Appendix.Listing8LoopFirstHaltFrames
public import SmcTuring.Appendix.Listing8GraphResetNodes

public section
namespace SmcTuring.Appendix.Listing8LoopFirstHalt
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8NodeTrace.finish mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule)) (Listing8GraphRun.finish mode origin l t g node rule memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphRun.program mode origin l t g node rule memory seed++((Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))).map StringControl.Form.previous).map StringStack.Form.previous

/-- Both continuations have the identical one-time original initialization. -/
theorem initial_same (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphRun.initial mode origin l t g node rule memory seed=Listing8GraphBackedge.initial mode origin l t g node rule memory seed := rfl

theorem input_entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    (Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode (Listing8GraphLayout.input mode origin g.transitions) := by
  have location:=(Listing8GraphRun.run mode origin l t g node rule ctx.nodeLocated ctx.ruleLocated ctx.resources ctx.fields ctx.copies ctx.boot ctx.body ctx.native halted memory seed).2.1
  simpa only [Arithmetic.encodeNat,BitVec.ofNat_toNat,BitVec.setWidth_eq] using congrArg (Arithmetic.encodeNat mode) location

theorem input_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringDword.Trace mode (Listing8GraphRun.finish mode origin l t g node rule memory seed)
      (Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule)))
      (finish mode origin l t g node rule memory seed) := by
  apply Listing8NodeTrace.trace mode _ _ (Listing8GraphNodeImage.valid mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.native_bounds mode origin g node rule ctx.native)) _ (input_entry mode origin l t g node rule ctx memory seed halted)
  rw [Listing8GraphStep.node_declarations]
  exact Listing8GraphResetNodes.initial mode origin l t g node rule ctx memory seed

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) := by
  rw [←initial_same]
  exact StringStack.trace_append mode (Listing8GraphRun.run mode origin l t g node rule ctx.nodeLocated ctx.ruleLocated ctx.resources ctx.fields ctx.copies ctx.boot ctx.body ctx.native halted memory seed).1
    (StringStack.previous_trace mode (StringControl.previous_trace mode (input_trace mode origin l t g node rule ctx memory seed halted)))

theorem result (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) ∧
    (finish mode origin l t g node rule memory seed).principal.memory=(Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.memory ∧
    (finish mode origin l t g node rule memory seed).principal.stack=(Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.stack ∧
    (finish mode origin l t g node rule memory seed).principal.carry=(Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.carry ∧
    (finish mode origin l t g node rule memory seed).sourceIndex=(Listing8GraphRun.finish mode origin l t g node rule memory seed).sourceIndex ∧
    (finish mode origin l t g node rule memory seed).destinationIndex=(Listing8GraphRun.finish mode origin l t g node rule memory seed).destinationIndex ∧
    (finish mode origin l t g node rule memory seed).backwards=(Listing8GraphRun.finish mode origin l t g node rule memory seed).backwards := by
  have nodes:=Listing8GraphResetNodes.initial mode origin l t g node rule ctx memory seed
  rw [←Listing8GraphStep.node_declarations] at nodes
  have actual:=Listing8NodeTrace.result mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
    (Listing8GraphNodeImage.valid mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.native_bounds mode origin g node rule ctx.native)) _ (input_entry mode origin l t g node rule ctx memory seed halted) nodes
  have ending : Listing8NodeTable.endPC mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))=Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
    rw [Listing8NodeTable.endPC,Listing8GraphNodeImage.length];rfl
  rw [ending] at actual
  exact actual

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=(if mode=.x86 then 156 else 207)+11*g.transitions+9*g.nodes := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphRun.program,Listing8FullTableReset.instruction_count,
    table_length,Listing8NodeTrace.instruction_count,Listing8GraphNodeImage.length]
  rfl

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule memory seed).principal.pc.toNat=Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  rw [(result mode origin l t g node rule ctx memory seed halted).1,Arithmetic.encode_nat_toNat mode _ ctx.native.capacity]

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    (finish mode origin l t g node rule memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule memory seed).backwards=false := by
  have actual:=result mode origin l t g node rule ctx memory seed halted
  have prior:=(Listing8GraphRun.run mode origin l t g node rule ctx.nodeLocated ctx.ruleLocated ctx.resources ctx.fields ctx.copies ctx.boot ctx.body ctx.native halted memory seed).2.2.2.2
  exact ⟨actual.2.2.1.trans prior.1,actual.2.2.2.1.trans prior.2.1,actual.2.2.2.2.1.trans prior.2.2.1,
    actual.2.2.2.2.2.1.trans prior.2.2.2.1,actual.2.2.2.2.2.2.trans prior.2.2.2.2⟩

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule)) (finish mode origin l t g node rule memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) (finish mode origin l t g node rule memory seed).principal.memory := by
  rw [(result mode origin l t g node rule ctx memory seed halted).2.1]
  constructor
  · rw [Listing8GraphStep.node_declarations];exact Listing8GraphResetNodes.initial mode origin l t g node rule ctx memory seed
  · exact Listing8LoopFirstHaltFrames.rules mode origin l t g node rule ctx memory seed

theorem tape_symbol (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) (query : Fin g.nodes) :
    DwordCode.get (finish mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g query+6)=
      ((Listing8GraphStep.updated g node rule).tape query).symbol := by
  rw [(result mode origin l t g node rule ctx memory seed halted).2.1]
  exact (Listing8GraphResetNodes.fields mode origin l t g node rule ctx memory seed query).1

theorem all_symbols (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    List.ofFn (fun query : Fin g.nodes => DwordCode.get (finish mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g query+6))=
      List.ofFn (fun query : Fin g.nodes => ((Listing8GraphStep.updated g node rule).tape query).symbol) :=
  congrArg List.ofFn (funext (tape_symbol mode origin l t g node rule ctx memory seed halted))

theorem logical_head_output (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    DwordCode.get (finish mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)+6)=
      ((Listing8GraphStep.updated g node rule).tape (Listing8GraphStep.nextNode g node rule)).symbol :=
  tape_symbol mode origin l t g node rule ctx memory seed halted _

end SmcTuring.Appendix.Listing8LoopFirstHalt

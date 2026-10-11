module
public import SmcTuring.Appendix.Listing8GraphHaltReturnWrites
public import SmcTuring.Appendix.Listing8GraphDeclarationWriteBounds
public import SmcTuring.Appendix.Listing8GraphResetWriteBounds
public import SmcTuring.Appendix.Listing8LoopFirstHalt

public section
namespace SmcTuring.Appendix.Listing8GraphHaltTerminalWrites
set_option maxHeartbeats 1000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def afterTable (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FullTable.finish mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) (table mode origin g)
    (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory)) seed
@[expose] def resetRegion (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) :=
  Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)
@[expose] def tableForms (mode : Mode) (origin : Nat) (g : Graph) :=
  (Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map (StringStoreWrites.liftDword mode)
@[expose] def resetForms (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) :=
  (Listing8ResetLayout.program mode (resetRegion mode origin l g)).map (StringStoreWrites.liftDword mode)
@[expose] def nodeForms (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  (Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions)
    (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))).map (StringStoreWrites.liftDword mode)
@[expose] def beforeNodes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8ResetEffects.finish mode (resetRegion mode origin l g) (afterTable mode origin l t g node rule memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphHaltReturnWrites.program mode origin l t g node rule memory seed++tableForms mode origin g++resetForms mode origin l g++nodeForms mode origin g node rule

theorem table_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphHaltReturnWrites.finish mode origin l t g node rule memory seed)
      (tableForms mode origin g) (afterTable mode origin l t g node rule memory seed) := by
  apply StringDwordWritesBridge.trace mode
  exact Listing8TableTrace.trace mode (Listing8FullTableImage.start mode origin) (table mode origin g)
    (reset_bounds mode origin l t g node rule ctx).declarations.valid
    (Listing8GraphHaltReturnWrites.finish mode origin l t g node rule memory seed)
    (by rw [Listing8GraphHaltReturnWrites.finish,Listing8FailReturn.effect mode origin l t (values mode origin g node rule)
      (nodePC mode origin g g.halt) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body];rfl)
    (Listing8FullTableImage.after_fail mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources
      (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx).declarations
      (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory)) seed)

theorem table_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (tableForms mode origin g) (Listing8GraphHaltReturnWrites.finish mode origin l t g node rule memory seed) := by
  exact Listing8DeclarationWrites.transitions_owned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    (Listing8FullTableImage.start mode origin) (table mode origin g) (reset_bounds mode origin l t g node rule ctx).declarations.valid
    (Listing8GraphDeclarationWriteBounds.transitions mode origin g ctx.native)
    (Listing8GraphHaltReturnWrites.finish mode origin l t g node rule memory seed)
    (by rw [Listing8GraphHaltReturnWrites.finish,Listing8FailReturn.effect mode origin l t (values mode origin g node rule)
      (nodePC mode origin g g.halt) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body];rfl)
    (Listing8FullTableImage.after_fail mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources
      (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx).declarations
      (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory)) seed)

theorem reset_entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (afterTable mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode (resetRegion mode origin l g).start :=
  (Listing8FullTable.result mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx).declarations
    (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory)) seed).1

theorem reset_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8ResetPackets.Initial mode (resetRegion mode origin l g) (afterTable mode origin l t g node rule memory seed).principal.memory :=
  Listing8TableResetImage.current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx)
    (Listing8GraphNodeImage.image mode origin g memory) seed

theorem reset_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (afterTable mode origin l t g node rule memory seed) (resetForms mode origin l g)
      (beforeNodes mode origin l t g node rule memory seed) :=
  StringDwordWritesBridge.trace mode (Listing8ResetTrace.trace mode (resetRegion mode origin l g) (reset_bounds mode origin l t g node rule ctx).reset
    (afterTable mode origin l t g node rule memory seed) (reset_entry mode origin l t g node rule ctx memory seed) (reset_current mode origin l t g node rule ctx memory seed))

theorem reset_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (resetForms mode origin l g) (afterTable mode origin l t g node rule memory seed) :=
  Listing8ResetWrites.owned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) (resetRegion mode origin l g)
    (reset_bounds mode origin l t g node rule ctx).reset (Listing8GraphResetWriteBounds.placement mode origin l t g node rule ctx)
    (afterTable mode origin l t g node rule memory seed) (reset_entry mode origin l t g node rule ctx memory seed) (reset_current mode origin l t g node rule ctx memory seed)

theorem nodes_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (beforeNodes mode origin l t g node rule memory seed) (nodeForms mode origin g node rule)
      (Listing8LoopFirstHalt.finish mode origin l t g node rule memory seed) :=
  StringDwordWritesBridge.trace mode (Listing8LoopFirstHalt.input_trace mode origin l t g node rule ctx memory seed halted)

theorem nodes_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (nodeForms mode origin g node rule) (beforeNodes mode origin l t g node rule memory seed) := by
  exact Listing8DeclarationWrites.nodes_owned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
    (Listing8GraphNodeImage.valid mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.native_bounds mode origin g node rule ctx.native))
    (Listing8GraphDeclarationWriteBounds.nodes mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.native_bounds mode origin g node rule ctx.native))
    (beforeNodes mode origin l t g node rule memory seed) (Listing8LoopFirstHalt.input_entry mode origin l t g node rule ctx memory seed halted)
    (by rw [Listing8GraphStep.node_declarations];exact Listing8GraphResetNodes.initial mode origin l t g node rule ctx memory seed)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) (program mode origin l t g node rule memory seed)
      (Listing8LoopFirstHalt.finish mode origin l t g node rule memory seed) :=
  StringStack.trace_append mode (StringStack.trace_append mode (StringStack.trace_append mode
    (Listing8GraphHaltReturnWrites.trace mode origin l t g node rule ctx memory seed halted) (table_trace mode origin l t g node rule ctx memory seed))
      (reset_trace mode origin l t g node rule ctx memory seed)) (nodes_trace mode origin l t g node rule ctx memory seed halted)

theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  unfold program
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ _ (beforeNodes mode origin l t g node rule memory seed)
    (StringStack.trace_append mode (StringStack.trace_append mode (Listing8GraphHaltReturnWrites.trace mode origin l t g node rule ctx memory seed halted)
      (table_trace mode origin l t g node rule ctx memory seed)) (reset_trace mode origin l t g node rule ctx memory seed))
  · apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      _ _ _ (afterTable mode origin l t g node rule memory seed)
      (StringStack.trace_append mode (Listing8GraphHaltReturnWrites.trace mode origin l t g node rule ctx memory seed halted)
        (table_trace mode origin l t g node rule ctx memory seed))
    · exact StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
        _ _ _ (Listing8GraphHaltReturnWrites.finish mode origin l t g node rule memory seed)
        (Listing8GraphHaltReturnWrites.trace mode origin l t g node rule ctx memory seed halted)
        (Listing8GraphHaltReturnWrites.owned mode origin l t g node rule ctx memory seed halted) (table_owned mode origin l t g node rule ctx memory seed)
    · exact reset_owned mode origin l t g node rule ctx memory seed
  · exact nodes_owned mode origin l t g node rule ctx memory seed halted

/-- The complete immediate-halt path, including every transition/reset/node
instruction, executes from one original initialization with all stores in code. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) (program mode origin l t g node rule memory seed)
      (Listing8LoopFirstHalt.finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  ⟨trace mode origin l t g node rule ctx memory seed halted,owned mode origin l t g node rule ctx memory seed halted⟩

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=(if mode=.x86 then 156 else 207)+11*g.transitions+9*g.nodes := by
  rw [program,List.length_append,List.length_append,List.length_append,Listing8GraphHaltReturnWrites.instruction_count,
    tableForms,resetForms,nodeForms,List.length_map,List.length_map,List.length_map,
    Listing8TableTrace.instruction_count,Listing8ResetLayout.instruction_count,Listing8NodeTrace.instruction_count,
    table_length,Listing8GraphNodeImage.length]
  rw [show (Listing8GraphStep.updated g node rule).nodes=g.nodes from rfl]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

end SmcTuring.Appendix.Listing8GraphHaltTerminalWrites

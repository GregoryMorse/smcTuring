module
public import SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates
public import SmcTuring.Appendix.Listing8GlobalControlProperties
public import SmcTuring.Appendix.Listing8GlobalDeclarationBindings
public import SmcTuring.Appendix.Listing8GlobalResetBindings
public import SmcTuring.Appendix.Listing8GraphHaltTerminalWrites

public section
namespace SmcTuring.Appendix.Listing8GlobalOriginalTerminalTemplates
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
attribute [local irreducible] StringTemplateStates.Run StringStoreRegions.Run
abbrev Targets:=Listing8PointerCopies.Targets

theorem halt_return (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8GraphHaltReturnWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  StringStackTraceDeterminism.transport mode _ _ _ _ _ _
    (by rw [Listing8GlobalOriginalControlTemplates.instruction_count,Listing8GraphHaltReturnWrites.instruction_count])
    (Listing8GlobalOriginalControlTemplates.execute mode origin l t g node rule ctx memory seed).1
    (Listing8GraphHaltReturnWrites.trace mode origin l t g node rule ctx memory seed halted)
    (Listing8GlobalOriginalControlTemplates.execute mode origin l t g node rule ctx memory seed).2

theorem reset_property (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GlobalControlTemplates.Property mode origin
      (Listing8GraphHaltTerminalWrites.beforeNodes mode origin l t g node rule memory seed).principal.memory := by
  have result:=Listing8FullTable.result mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx).declarations
    (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g)
      (Listing8GraphNodeImage.image mode origin g memory)) seed
  have initial : Listing8GlobalControlTemplates.Property mode origin
      (Listing8GraphHaltTerminalWrites.afterTable mode origin l t g node rule memory seed).principal.memory := by
    rw [Listing8GraphHaltTerminalWrites.afterTable,result.2.1]
    exact Listing8GlobalControlTemplates.initial mode origin _
      (Listing8GlobalControlBindings.original_current mode origin l t (values mode origin g node rule)
        (nodePC mode origin g g.halt) (Listing8FullTableImage.start mode origin) ctx.resources (owners mode origin l t g node rule ctx)
        ctx.copies ctx.boot ctx.body (Listing8GraphNextFailImage.tail_bounds mode origin l t g node rule ctx)
        (Listing8GraphHaltReturnWrites.backing mode origin l g memory) seed)
  have bounds:=(reset_bounds mode origin l t g node rule ctx).reset
  have entry:=Listing8GraphHaltTerminalWrites.reset_entry mode origin l t g node rule ctx memory seed
  have current:=Listing8GraphHaltTerminalWrites.reset_current mode origin l t g node rule ctx memory seed
  have actual:=Listing8GraphHaltTerminalWrites.reset_trace mode origin l t g node rule ctx memory seed
  have identity:=Listing8GraphReset.actual_region mode origin l t (nodePC mode origin g g.halt) (table mode origin g) ctx.boot ctx.body
  rw [table_length] at identity
  change _=Arithmetic.encodeNat mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)).start at entry
  change Listing8ResetPackets.Initial mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)) _ at current
  change StringStack.Trace mode (Listing8GraphHaltTerminalWrites.afterTable mode origin l t g node rule memory seed)
    ((Listing8ResetLayout.program mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))).map (StringStoreWrites.liftDword mode))
    (Listing8GraphHaltTerminalWrites.beforeNodes mode origin l t g node rule memory seed) at actual
  rw [identity] at bounds entry current actual
  exact Listing8GlobalControlProperties.after_trace mode origin _ _ _ initial
    (Listing8GlobalControlRegions.reset mode origin g.transitions bounds _ entry current) actual

theorem nodes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8GraphHaltTerminalWrites.nodeForms mode origin g node rule)
      (Listing8GraphHaltTerminalWrites.beforeNodes mode origin l t g node rule memory seed) := by
  have current : Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8GraphHaltTerminalWrites.beforeNodes mode origin l t g node rule memory seed).principal.memory := by
    rw [Listing8GraphStep.node_declarations]
    exact Listing8GraphResetNodes.initial mode origin l t g node rule ctx memory seed
  exact StringTemplateStates.monotone mode _ _ _ _ (fun _ kept => kept.1)
    (Listing8GlobalDeclarationBindings.nodes mode origin (Listing8GraphStep.updated g node rule)
      (Listing8GraphStep.native_bounds mode origin g node rule ctx.native) _
      (Listing8LoopFirstHalt.input_entry mode origin l t g node rule ctx memory seed halted)
      current (reset_property mode origin l t g node rule ctx memory seed))

theorem property (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    Listing8GlobalControlTemplates.Property mode origin
      (Listing8LoopFirstHalt.finish mode origin l t g node rule memory seed).principal.memory := by
  rw [(Listing8LoopFirstHalt.result mode origin l t g node rule ctx memory seed halted).2.1]
  exact reset_property mode origin l t g node rule ctx memory seed

/-- The immediate original halt still executes its entire first body, real
CALL/FAIL target, every transition, reset and every updated node declaration.
All global control descriptors decode at the same every reached prefix. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (Listing8GraphHaltTerminalWrites.program mode origin l t g node rule memory seed)
      (Listing8LoopFirstHalt.finish mode origin l t g node rule memory seed) ∧
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8GraphHaltTerminalWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  have first:=Listing8GraphHaltReturnWrites.trace mode origin l t g node rule ctx memory seed halted
  have table:=Listing8GraphHaltTerminalWrites.table_trace mode origin l t g node rule ctx memory seed
  have reset:=Listing8GraphHaltTerminalWrites.reset_trace mode origin l t g node rule ctx memory seed
  refine ⟨Listing8GraphHaltTerminalWrites.trace mode origin l t g node rule ctx memory seed halted,?_⟩
  rw [Listing8GraphHaltTerminalWrites.program,StringTemplateStates.append,StringTemplateStates.append,StringTemplateStates.append]
  rw [StringWrites.trace_run_eq mode first,
    StringWrites.trace_run_eq mode (StringStack.trace_append mode first table),
    StringWrites.trace_run_eq mode (StringStack.trace_append mode (StringStack.trace_append mode first table) reset)]
  refine ⟨⟨⟨halt_return mode origin l t g node rule ctx memory seed halted,?_⟩,?_⟩,
    nodes mode origin l t g node rule ctx memory seed halted⟩
  · exact StringTemplateStates.monotone mode _ _ _ _ (fun _ kept => kept.1)
      (Listing8GlobalDeclarationBindings.original_graph mode origin l t g node rule ctx (Listing8GraphNodeImage.image mode origin g memory) seed)
  · exact StringTemplateStates.monotone mode _ _ _ _ (fun _ kept => kept.1)
      (Listing8GlobalResetBindings.original_graph mode origin l t g node rule ctx (Listing8GraphNodeImage.image mode origin g memory) seed)

end SmcTuring.Appendix.Listing8GlobalOriginalTerminalTemplates

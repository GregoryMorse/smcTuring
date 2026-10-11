module
public import SmcTuring.Appendix.Listing8ResetExecutableTemplates
public import SmcTuring.Appendix.Listing8LoopReset

public section
namespace SmcTuring.Appendix.Listing8ResetTemplateBindings
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem graph_separation (mode : Mode) (origin transitions : Nat) (positive : 0<transitions) :
    Listing8ResetTemplateFields.Separation mode (Listing8GraphReset.region mode origin transitions) := by
  cases mode <;> constructor
  all_goals simp only [Listing8GraphReset.region,Listing8GraphLayout.reset,Listing8GraphLayout.transition,
    Listing8FullTableImage.start,Listing8FailLayout.end_offset,Mode.wordBytes,reduceCtorEq,ite_true,ite_false,
    Listing8ResetLayout.endPC,Listing8ResetLayout.markerPC,Listing8ResetLayout.transitionCopy,Listing8ResetLayout.ownerPC,
    Listing8ResetLayout.inputCopy,ConversionLayout.endPC,ConversionLayout.thirdPC,ConversionLayout.secondPC,
    ConversionLayout.exchangeSize,ConversionLayout.storeSize,StringCodec.initialSize,instructionLength,
    MemoryOp.prefix,MemoryOp.trailer,wordPrefix,Listing8Prototypes.transitionSpan,Listing8Prototypes.pointerSpan,
    ReaderImage.totalSize,List.length_nil,List.length_cons]
  all_goals omega

theorem actual_separation (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing8ResetTemplateFields.Separation mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)) := by
  rw [Listing8GraphReset.actual_region mode origin l t _ _ ctx.boot ctx.body,table_length]
  exact graph_separation mode origin g.transitions (by have bound:=rule.isLt;omega)

/-- The original image constructs the reached reset packets and CALL header,
including execution of every original transition declaration. -/
theorem original_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let reset:=Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)
    let reached:=Listing8FullTable.finish mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (table mode origin g) (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) memory) seed
    StringTemplateStates.Run mode (fun state => Listing8ResetExecutableTemplates.Decodes mode reset state.principal.memory)
      ((Listing8ResetLayout.program mode reset).map (StringStoreWrites.liftDword mode)) reached := by
  have located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) rule.val := by
    rw [ctx.ruleLocated];rfl
  have bounds:=Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx
  have result:=Listing8FullTable.result mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (table mode origin g) rule.val (Listing8SourceGraph.selected mode origin g node rule) located
    ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body bounds.declarations
    (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) memory) seed
  apply Listing8ResetExecutableTemplates.all_decodes mode _ bounds.reset (actual_separation mode origin l t g node rule ctx) _ result.1
    (Listing8TableResetImage.current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (table mode origin g) rule.val (Listing8SourceGraph.selected mode origin g node rule) located
      ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body bounds memory seed)
  rw [result.2.1]
  exact RelativeCallTemplate.initial mode _ _ _ (Listing8GlobalJump.call_packet mode origin l t (values mode origin g node rule)
    (nodePC mode origin g g.halt) ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx)
    ctx.copies ctx.boot ctx.body _ seed)

theorem selected_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    let reset:=Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)
    StringTemplateStates.Run mode (fun state => Listing8ResetExecutableTemplates.Decodes mode reset state.principal.memory)
      ((Listing8ResetLayout.program mode reset).map (StringStoreWrites.liftDword mode))
      (Listing8GraphNextTable.finish mode origin l t g node rule target memory seed) := by
  apply Listing8ResetExecutableTemplates.all_decodes mode _ (Listing8GraphNextResetImage.bounds mode origin l t g node rule ctx)
    (actual_separation mode origin l t g node rule ctx) _
    (Listing8GraphNextTable.endpoint mode origin l t g node rule target ctx selected memory seed halted)
    (Listing8GraphNextResetImage.after_table mode origin l t g node rule target ctx selected memory seed halted)
  rw [Listing8GraphNextTable.memory_effect mode origin l t g node rule target ctx selected memory seed halted]
  exact RelativeCallTemplate.initial mode _ _ _ (Listing8GraphNextJump.call_packet mode origin l t g node rule target ctx selected memory seed)

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) (old : Listing8MainInput.OldInput)
    (state : StringExecution.State mode) (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringTemplateStates.Run mode (fun reached => Listing8ResetExecutableTemplates.Decodes mode
      (Listing8LoopHaltImage.region mode origin l g) reached.principal.memory)
      ((Listing8ResetLayout.program mode (Listing8LoopHaltImage.region mode origin l g)).map (StringStoreWrites.liftDword mode))
      (Listing8LoopTable.finish mode origin l t g node rule state) := by
  apply Listing8ResetExecutableTemplates.all_decodes mode _ (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset
    (actual_separation mode origin l t g node rule ctx) _
    (Listing8LoopTable.endpoint mode origin l t g node rule ctx old state image.control halted)
    (Listing8LoopHaltImage.after_table mode origin l t g node rule ctx old state image halted)
  rw [(Listing8LoopTable.result mode origin l t g node rule ctx old state image.control halted).2.1,
    Listing8LoopControl.memory mode origin l t g node rule ctx old state image.control]
  exact RelativeCallTemplate.initial mode _ _ _ (Listing8LoopControl.current mode origin l t g node rule ctx old state image.control).callImage

end SmcTuring.Appendix.Listing8ResetTemplateBindings

module
public import SmcTuring.Appendix.Listing8GlobalControlBindings

public section
namespace SmcTuring.Appendix.Listing8GlobalResetBindings
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

/-- Global control validity and local reset validity hold at exactly the same
reached reset prefixes, including the changing live CALL displacement. -/
theorem original_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let reset:=Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)
    let reached:=Listing8FullTable.finish mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (table mode origin g) (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) memory) seed
    StringTemplateStates.Run mode (fun state => Listing8GlobalControlTemplates.Decodes mode origin state.principal.memory ∧
      Listing8ResetExecutableTemplates.Decodes mode reset state.principal.memory)
      ((Listing8ResetLayout.program mode reset).map (StringStoreWrites.liftDword mode)) reached := by
  dsimp only
  apply JointTemplateStates.join mode _ _ _ _
    _ (Listing8ResetTemplateBindings.original_graph mode origin l t g node rule ctx memory seed)
  have located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) rule.val := by
    rw [ctx.ruleLocated];rfl
  have bounds:=Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx
  have result:=Listing8FullTable.result mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (table mode origin g) rule.val (Listing8SourceGraph.selected mode origin g node rule) located
    ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body bounds.declarations
    (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) memory) seed
  apply Listing8GlobalControlTemplates.all_decodes mode origin _ _
  · rw [result.2.1]
    exact Listing8GlobalControlTemplates.initial mode origin _
      (Listing8GlobalControlBindings.original_current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8FullTableImage.start mode origin) ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx)
        ctx.copies ctx.boot ctx.body
        (Listing8FullTableImage.fail_bounds mode origin l (table mode origin g) rule.val (values mode origin g node rule) (Listing8SourceGraph.selected mode origin g node rule)
          located bounds.declarations) _ seed)
  · have current:=Listing8TableResetImage.current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (table mode origin g) rule.val (Listing8SourceGraph.selected mode origin g node rule) located
      ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body bounds memory seed
    have identity:=Listing8GraphReset.actual_region mode origin l t (nodePC mode origin g g.halt) (table mode origin g) ctx.boot ctx.body
    rw [table_length] at identity
    have resetBounds:=bounds.reset
    have entry : (Listing8FullTable.finish mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (table mode origin g) (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) memory) seed).principal.pc=
        Arithmetic.encodeNat mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)).start := result.1
    rw [identity] at resetBounds entry current ⊢
    exact Listing8GlobalControlRegions.reset mode origin g.transitions resetBounds _ entry current

theorem selected_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    let reset:=Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)
    StringTemplateStates.Run mode (fun state => Listing8GlobalControlTemplates.Decodes mode origin state.principal.memory ∧
      Listing8ResetExecutableTemplates.Decodes mode reset state.principal.memory)
      ((Listing8ResetLayout.program mode reset).map (StringStoreWrites.liftDword mode))
      (Listing8GraphNextTable.finish mode origin l t g node rule target memory seed) := by
  dsimp only
  apply JointTemplateStates.join mode _ _ _ _
    _ (Listing8ResetTemplateBindings.selected_graph mode origin l t g node rule target ctx selected memory seed halted)
  apply Listing8GlobalControlTemplates.all_decodes mode origin _ _
  · rw [Listing8GraphNextTable.memory_effect mode origin l t g node rule target ctx selected memory seed halted]
    exact Listing8GlobalControlTemplates.initial mode origin _
      (Listing8GlobalControlBindings.selected_current mode origin l t g node rule target ctx selected memory seed)
  · have bounds:=Listing8GraphNextResetImage.bounds mode origin l t g node rule ctx
    have entry:=Listing8GraphNextTable.endpoint mode origin l t g node rule target ctx selected memory seed halted
    have current:=Listing8GraphNextResetImage.after_table mode origin l t g node rule target ctx selected memory seed halted
    have identity:=Listing8GraphReset.actual_region mode origin l t (nodePC mode origin g g.halt) (table mode origin g) ctx.boot ctx.body
    rw [table_length] at identity
    rw [identity] at bounds entry current ⊢
    exact Listing8GlobalControlRegions.reset mode origin g.transitions bounds _ entry current

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) (old : Listing8MainInput.OldInput)
    (state : StringExecution.State mode) (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8ResetExecutableTemplates.Decodes mode (Listing8LoopHaltImage.region mode origin l g) reached.principal.memory)
      ((Listing8ResetLayout.program mode (Listing8LoopHaltImage.region mode origin l g)).map (StringStoreWrites.liftDword mode))
      (Listing8LoopTable.finish mode origin l t g node rule state) := by
  apply JointTemplateStates.join mode _ _ _ _
    _ (Listing8ResetTemplateBindings.maintained mode origin l t g node rule ctx old state image halted)
  apply Listing8GlobalControlTemplates.all_decodes mode origin _ _
  · rw [(Listing8LoopTable.result mode origin l t g node rule ctx old state image.control halted).2.1,
      Listing8LoopControl.memory mode origin l t g node rule ctx old state image.control]
    exact Listing8GlobalControlTemplates.initial mode origin _
      (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image.control)
  · have bounds:=(Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset
    have entry:=Listing8LoopTable.endpoint mode origin l t g node rule ctx old state image.control halted
    have current:=Listing8LoopHaltImage.after_table mode origin l t g node rule ctx old state image halted
    have identity:=Listing8GraphReset.actual_region mode origin l t (nodePC mode origin g g.halt) (table mode origin g) ctx.boot ctx.body
    rw [table_length] at identity
    change Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)=_ at identity
    change StringStoreRegions.Run mode _ ((Listing8ResetLayout.program mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))).map _) _
    change _=Arithmetic.encodeNat mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)).start at entry
    change Listing8ResetPackets.Initial mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)) _ at current
    rw [identity] at bounds entry current ⊢
    exact Listing8GlobalControlRegions.reset mode origin g.transitions bounds _ entry current

end SmcTuring.Appendix.Listing8GlobalResetBindings

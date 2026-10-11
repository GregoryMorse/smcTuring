module
public import SmcTuring.Appendix.Listing8GlobalDeclarationRegions
public import SmcTuring.Appendix.Listing8DeclarationOwnerRegions
public import SmcTuring.Appendix.Listing8GlobalControlBindings

public section
namespace SmcTuring.Appendix.Listing8GlobalDeclarationBindings
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

/-- Both certificates observe the same reached memory. The declaration
exception is its exact active word; all global control headers remain valid. -/
theorem nodes (mode : Mode) (origin : Nat) (g : Graph) (bounds : Listing8GraphPointers.Bounds mode origin g)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8GraphLayout.input mode origin g.transitions))
    (current : Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin g) state.principal.memory)
    (intact : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8OriginalOwnerRegions.Certificate mode
        (Listing8NodeTable.owners mode (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin g))
        state.principal.memory reached.principal.memory)
      ((Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions)
        (Listing8GraphNodeImage.declarations mode origin g)).map (StringStoreWrites.liftDword mode)) state :=
  JointTemplateStates.join mode _ _ _ state
    (Listing8GlobalControlTemplates.all_decodes mode origin _ state intact
      (Listing8GlobalDeclarationRegions.node_regions mode origin g bounds state entry current))
    (Listing8DeclarationOwnerRegions.nodes mode _ _ (Listing8GraphNodeImage.valid mode origin g bounds) state entry current).2

theorem transitions (mode : Mode) (origin : Nat) (g : Graph) (bounds : Listing8GraphPointers.Bounds mode origin g)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin))
    (current : Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) state.principal.memory)
    (intact : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8OriginalOwnerRegions.Certificate mode (Listing8TransitionTable.owners mode (Listing8FullTableImage.start mode origin) (table mode origin g))
        state.principal.memory reached.principal.memory)
      ((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map (StringStoreWrites.liftDword mode)) state :=
  JointTemplateStates.join mode _ _ _ state
    (Listing8GlobalControlTemplates.all_decodes mode origin _ state intact
      (Listing8GlobalDeclarationRegions.transition_regions mode origin g bounds state entry current))
    (Listing8DeclarationOwnerRegions.transitions mode _ _ (Listing8GraphTableBounds.declarations_valid mode origin g bounds) state entry current).2

theorem original_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let reached:=Listing8FullTable.entryState mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (table mode origin g) (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) memory) seed
    StringTemplateStates.Run mode (fun state => Listing8GlobalControlTemplates.Decodes mode origin state.principal.memory ∧
      Listing8OriginalOwnerRegions.Certificate mode (Listing8TransitionTable.owners mode (Listing8FullTableImage.start mode origin) (table mode origin g))
        reached.principal.memory state.principal.memory)
      ((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map (StringStoreWrites.liftDword mode)) reached := by
  dsimp only
  have bounds:=(Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).declarations
  have located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) rule.val := by
    rw [ctx.ruleLocated];rfl
  apply transitions mode origin g ctx.native _
  · rw [Listing8FullTable.entryState,Listing8FailReturn.effect mode origin l t _ _ ctx.resources
      (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body]
    rfl
  · exact Listing8FullTableImage.after_fail mode origin l t _ _ (table mode origin g) rule.val
      (Listing8SourceGraph.selected mode origin g node rule) located ctx.resources
      (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body bounds _ seed
  · rw [Listing8FullTable.entryState,Listing8FailReturn.effect mode origin l t _ _ ctx.resources
      (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body]
    exact Listing8GlobalControlTemplates.initial mode origin _
      (Listing8GlobalControlBindings.original_current mode origin l t _ _ (Listing8FullTableImage.start mode origin) ctx.resources
        (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
        (Listing8FullTableImage.fail_bounds mode origin l (table mode origin g) rule.val (values mode origin g node rule)
          (Listing8SourceGraph.selected mode origin g node rule) located bounds) _ seed)

theorem selected_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    let reached:=Listing8GraphNextFailReturn.finish mode origin l t g node rule target memory seed
    StringTemplateStates.Run mode (fun state => Listing8GlobalControlTemplates.Decodes mode origin state.principal.memory ∧
      Listing8OriginalOwnerRegions.Certificate mode (Listing8TransitionTable.owners mode (Listing8FullTableImage.start mode origin) (table mode origin g))
        reached.principal.memory state.principal.memory)
      ((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map (StringStoreWrites.liftDword mode)) reached := by
  dsimp only
  apply transitions mode origin g ctx.native _
    (Listing8GraphNextFailReturn.registers mode origin l t g node rule target ctx selected memory seed halted).1
    (Listing8GraphNextFailReturn.source_graph mode origin l t g node rule target ctx selected memory seed halted).2
  rw [Listing8GraphNextFailReturn.effect mode origin l t g node rule target ctx selected memory seed halted]
  exact Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.selected_current mode origin l t g node rule target ctx selected memory seed)

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) (old : Listing8MainInput.OldInput)
    (state : StringExecution.State mode) (image : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    let reached:=Listing8LoopControl.finish mode origin l t g node rule state
    StringTemplateStates.Run mode (fun machine => Listing8GlobalControlTemplates.Decodes mode origin machine.principal.memory ∧
      Listing8OriginalOwnerRegions.Certificate mode (Listing8TransitionTable.owners mode (Listing8FullTableImage.start mode origin) (table mode origin g))
        reached.principal.memory machine.principal.memory)
      ((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map (StringStoreWrites.liftDword mode)) reached := by
  dsimp only
  apply transitions mode origin g ctx.native _ (Listing8LoopTable.table_entry mode origin l t g node rule ctx old state image halted)
    (Listing8LoopControlFrames.source_graph mode origin l t g node rule ctx old state image).2
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)

end SmcTuring.Appendix.Listing8GlobalDeclarationBindings

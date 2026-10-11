module
public import SmcTuring.Appendix.Listing8MacroRetargetFrames
public import SmcTuring.Appendix.Listing8JointControlCatalog
public import SmcTuring.Appendix.Listing8JointRetargetControl
public import SmcTuring.Appendix.Listing8JointCopyOwnerPrefixes

public section
namespace SmcTuring.Appendix.Listing8JointMainMacroCatalog
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets
abbrev Catalog:=Listing8JointCopyOwnerPrefixes.Catalog

theorem retarget (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerCatalog.Property mode origin l reached.principal.memory)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) (Listing8MainCopies.finish mode l state) := by
  have copyTrace:=(Listing8GraphCopyOwnerPrefixes.live mode origin l t g node rule ctx state entry forward current).1
  have globalAt:=Listing8GlobalControlProperties.after_trace mode origin _ _ _ global
    (Listing8GlobalCopyRegions.regions mode origin l t g node rule ctx state entry forward current) copyTrace
  have globalRun:=Listing8GlobalControlTemplates.all_decodes mode origin _ _ globalAt
    (Listing8GlobalRetargetRegions.retarget mode origin l t g node rule ctx _
      (Listing8MainCopies.registers mode l _ ctx.resources state entry forward current).1
      (Listing8MainCopies.retarget_current mode l _ ctx.resources state entry forward current))
  have localRun:=Listing8RetargetTapeTemplates.actual_copies mode l _ ctx.resources ctx.fields.tapeReach state entry forward current
  have macros:=Listing8MacroRetargetFrames.all_states mode l _ ctx.resources ctx.fields.tapeReach state entry forward current
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun reached all => show Listing8JointOwnerPointerCatalog.Property mode origin l reached.principal.memory from
      ⟨all.1.1,all.1.2,StringEncodedTemplates.macro_decodes mode _ _ ctx.resources.node.sizeFits all.2.1,
        StringEncodedTemplates.macro_decodes mode _ _ ctx.resources.transition.sizeFits all.2.2⟩)
    (JointTemplateStates.join mode _ _ _ _ (JointTemplateStates.join mode _ _ _ _ globalRun localRun) macros)

theorem copy_retarget (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (Catalog mode origin l)
      ((Listing8MainRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  rw [Listing8JointRetargetControl.shape,StringTemplateStates.append,
    StringWrites.trace_run_eq mode (Listing8GraphCopyOwnerPrefixes.live mode origin l t g node rule ctx state entry forward current).1]
  exact ⟨Listing8CrossMacroCatalog.pair mode origin l t g node rule ctx state entry forward current global,
    StringTemplateStates.monotone mode _ _ _ _ (fun _ all => ⟨all.1,all.2.2.1,all.2.2.2⟩)
      (retarget mode origin l t g node rule ctx state entry forward current global)⟩

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (Catalog mode origin l)
      (Listing8LoopControl.program mode origin l t g node rule state) state := by
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have trace:=StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources state
    image.body.state.head.graph.entry image.body.state.head.graph.forward current.state.head.input.prefixCurrent.copying)
  have shape : Listing8LoopControl.program mode origin l t g node rule state=
      (Listing8MainRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)++
        Listing8JointControlCatalog.suffix mode origin l t g node rule state := by
    rw [Listing8LoopControl.program,Listing8JointControlCatalog.prefix_forms,Listing8JointControlCatalog.suffix,List.append_assoc]
  rw [shape,StringTemplateStates.append,StringWrites.trace_run_eq mode trace]
  exact ⟨copy_retarget mode origin l t g node rule ctx state image.body.state.head.graph.entry image.body.state.head.graph.forward
      current.state.head.input.prefixCurrent.copying global,
    StringTemplateStates.monotone mode _ _ _ _ (fun _ all => ⟨all.1.1,all.1.2.2.1,all.1.2.2.2⟩)
      (Listing8JointControlCatalog.through_control mode origin l t g node rule ctx old state image global)⟩

theorem after_copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerCatalog.Property mode origin l reached.principal.memory)
      (((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))++Listing8JointControlCatalog.suffix mode origin l t g node rule state)
      (Listing8MainCopies.finish mode l state) := by
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have trace:=StringDwordWritesBridge.trace mode (Listing8MainRetarget.retarget_trace mode l _ ctx.resources state
    image.body.state.head.graph.entry image.body.state.head.graph.forward current.state.head.input.prefixCurrent.copying)
  rw [StringTemplateStates.append,StringWrites.trace_run_eq mode trace]
  exact ⟨retarget mode origin l t g node rule ctx state image.body.state.head.graph.entry image.body.state.head.graph.forward
      current.state.head.input.prefixCurrent.copying global,
    StringTemplateStates.monotone mode _ _ _ _ (fun _ all => all.1)
      (Listing8JointControlCatalog.through_control mode origin l t g node rule ctx old state image global)⟩

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (Catalog mode origin l)
      (Listing8LoopControl.program mode origin l t g node rule state) state := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  exact main mode origin l t g node rule ctx old state image initialGlobal

theorem original_prefix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (Catalog mode origin l)
      ((Listing8MainRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have initial:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalInitialControl.current mode origin l t g node rule ctx memory seed)
  have actual:=Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  change StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
    (Listing4EntryLayout.forms mode origin) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) at actual
  have regions:=BoundedStoreRegions.monotone mode (Listing4StackTemplates.Slots mode origin) (Listing8GlobalControlLayout.Allowed mode origin)
    (Listing4EntryLayout.forms mode origin) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
    (fun _ _ slots => Or.inl slots)
    (Listing4EntrySlotRegions.entry mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))
  apply copy_retarget mode origin l t g node rule ctx _ _ _
    (Listing8GlobalOriginalPrefix.copying mode origin l t g node rule ctx memory seed)
    (Listing8GlobalControlProperties.after_trace mode origin _ _ _ initial regions actual)
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl

end SmcTuring.Appendix.Listing8JointMainMacroCatalog

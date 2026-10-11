module
public import SmcTuring.Appendix.Listing8ControlStoreFields
public import SmcTuring.Appendix.Listing8JointFailureCatalog
public import SmcTuring.Appendix.Listing8LoopControlCases

public section
namespace SmcTuring.Appendix.Listing8JointControlCatalog
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def earlier (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  Listing8JointFailureCatalog.earlier mode l t (values mode origin g node rule) state++
    Listing8JointFailureCatalog.forms mode origin l g (Listing8LoopState.finish mode l t (values mode origin g node rule) state)
@[expose] def suffix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  earlier mode origin l t g node rule state++Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state)

theorem prefix_forms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    (Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous=
      (Listing8MainRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)++earlier mode origin l t g node rule state := by
  simp only [Listing8LoopFailure.program,List.map_append,Listing8GlobalLoopMainRegions.lift_dword,
    Listing8JointFailureCatalog.prefix_forms,earlier,Listing8JointFailureCatalog.forms,
    Listing8FailureCrossCatalogFields.region,List.append_assoc]

theorem prefix_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringStack.Trace mode (Listing8MainRetarget.finish mode l (values mode origin g node rule) state)
      (earlier mode origin l t g node rule state) (Listing8LoopControl.failureEnd mode origin l t g node rule state) := by
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have whole:=Listing8LoopGraphFailure.trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
    (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) current.body
  rw [prefix_forms] at whole
  exact StringTracePrefixes.tail mode _ _ _ _ _ whole
    (StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources state current.body.state.head.graph.entry
      current.body.state.head.graph.forward image.state.head.input.prefixCurrent.copying))

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)
      (Listing8LoopControl.failureEnd mode origin l t g node rule state).principal.memory := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have entry:=current.body.state.head.graph.entry
  have forward:=current.body.state.head.graph.forward
  have position:=Listing8LoopState.endpoint mode l t _ old b.state state entry forward image.state
  have ready:=Listing8LoopFailurePrefix.current_after_state mode l t _ old _ _ b state entry forward image
  have core:=StringStoreTemplateRuns.preserve mode (Listing8FailureCrossCatalogFields.Allowed mode origin l g)
    (Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)) _ _
    (Listing8JointFailureCatalog.initial mode origin l t g node rule ctx old state current.body.state)
    (Listing8FailureCrossCatalogFields.store mode origin l t g node rule ctx)
    (Listing8FailureCrossCatalogFields.regions mode origin l t g node rule ctx _ position ready)
  exact Listing8InputCatalogInitial.endpoint mode _ _ _ _ core
    (StringStack.previous_trace mode (Listing8LoopFailure.failure_trace mode l t _ _ _ old b state entry forward image))

theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l
      (values mode origin g node rule) reached.principal.memory)
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.failureEnd mode origin l t g node rule state) := by
  have position:=Listing8LoopControl.entry mode origin l t g node rule ctx old state current
  have capacity:=Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  have ready:=Listing8LoopControl.current mode origin l t g node rule ctx old state current
  have globalAt:=Listing8GlobalControlProperties.after_trace mode origin _ _ _ global
    (Listing8GlobalLoopMainRegions.failure mode origin l t g node rule ctx old state current.body)
    (Listing8LoopGraphFailure.trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
      (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) current.body)
  have globalRun:=Listing8GlobalControlTemplates.all_decodes mode origin _ _ globalAt
    (Listing8GlobalControlRegions.jump mode origin _ _ position capacity ready)
  have core:=Listing8ControlStoreFields.all_states mode origin l t g node rule ctx _ _ position capacity ready
    (initial mode origin l t g node rule ctx old state current)
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun reached all => show Listing8JointOwnerPointerPurity.Property mode origin l (values mode origin g node rule) reached.principal.memory from
      ⟨⟨all.1,(fun template member => DwordTemplateCollection.decodes mode template reached.principal.memory (all.2.1 template member)),
          StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.node.sizeFits all.2.2.1.1,
          StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.transition.sizeFits all.2.2.1.2⟩,
        Listing8CopiedOwnerActiveRun.empty mode _ reached.principal.memory all.2.2.2⟩)
    (JointTemplateStates.join mode _ _ _ _ globalRun core)

theorem through_control (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l
      (values mode origin g node rule) reached.principal.memory)
      (suffix mode origin l t g node rule state) (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  rw [suffix,StringTemplateStates.append,StringWrites.trace_run_eq mode (prefix_trace mode origin l t g node rule ctx old state current)]
  exact ⟨Listing8JointFailureCatalog.through_failure mode origin l t g node rule ctx old state current global,
    main mode origin l t g node rule ctx old state current global⟩

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)
      (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory :=
  Listing8InputCatalogInitial.endpoint mode _ _ _ _
    (Listing8ControlStoreFields.all_states mode origin l t g node rule ctx _ _
      (Listing8LoopControl.entry mode origin l t g node rule ctx old state current)
      (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
      (Listing8LoopControl.current mode origin l t g node rule ctx old state current)
      (initial mode origin l t g node rule ctx old state current))
    (Listing8LoopControl.return_trace mode origin l t g node rule ctx old state current)

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOwnerPointerPurity.Property mode origin l
      (values mode origin g node rule) reached.principal.memory)
      (suffix mode origin l t g node rule state) (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have actual:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image).1
  have ending:=Listing8GlobalControlTemplates.initial mode origin _
    (Listing8GlobalControlBindings.maintained_current mode origin l t g node rule ctx old state image)
  have initialGlobal:=Listing8JointMacroControl.initial_property mode origin _ state
    (Listing8GlobalMainControlTemplates.regions mode origin l t g node rule ctx old state image) (by
      rw [StringWrites.trace_run_eq mode actual,Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
      exact ending)
  exact through_control mode origin l t g node rule ctx old state image initialGlobal

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    (suffix mode origin l t g node rule state).length=if mode=.x86 then 89 else 130 := by
  have shape : Listing8LoopControl.program mode origin l t g node rule state=
      (Listing8MainRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)++suffix mode origin l t g node rule state := by
    rw [Listing8LoopControl.program,prefix_forms,suffix,List.append_assoc]
  have count:=congrArg List.length shape
  rw [Listing8LoopControl.instruction_count,List.length_append,List.length_map,Listing8MainRetarget.instruction_count] at count
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at count ⊢ <;> omega

theorem returned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Listing8InputCatalogInitial.Property mode l (values mode origin g node rule)
      (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory ∧
    ((Listing8GraphRun.Halted g node rule ∧ (Listing8LoopControl.finish mode origin l t g node rule state).principal.pc=Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin)) ∨
      (¬Listing8GraphRun.Halted g node rule ∧ (Listing8LoopControl.finish mode origin l t g node rule state).principal.pc=Arithmetic.encodeNat mode l.start)) := by
  refine ⟨endpoint mode origin l t g node rule ctx old state current,?_⟩
  by_cases halted : Listing8GraphRun.Halted g node rule
  · left;refine ⟨halted,?_⟩
    rw [Listing8LoopControl.endpoint mode origin l t g node rule ctx old state current,
      Listing8LoopControlCases.failure mode origin l t g node rule ctx old state current halted]
    rfl
  · right;refine ⟨halted,?_⟩
    rw [Listing8LoopControl.endpoint mode origin l t g node rule ctx old state current,
      Listing8LoopControlCases.nonfailure mode origin l t g node rule ctx old state current halted]
    rfl

end SmcTuring.Appendix.Listing8JointControlCatalog

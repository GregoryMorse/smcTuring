module
public import SmcTuring.Native.StringTemplateTraceSegments
public import SmcTuring.Appendix.Listing8GlobalMainControlTemplates
public import SmcTuring.Appendix.Listing8JointTemplateBindings
public import SmcTuring.Appendix.Listing8HeadTemplateBindings
public import SmcTuring.Appendix.Listing8StateTemplateBindings
public import SmcTuring.Appendix.Listing8FailureTemplateBindings

public section
namespace SmcTuring.Appendix.Listing8MaintainedJointPhases
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

/-- Global control and local executable validity refer to the same actual phase. -/
theorem input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      (∀ window∈MixedTemplateGeometry.windows mode l.input.start (Listing8LiteralComposition.program mode l.input (values mode origin g node rule).rule (values mode origin g node rule).tape (values mode origin g node rule).fresh), Listing8InputJointTemplates.ValidWindow mode window reached.principal.memory))
      (((Listing8LiteralComposition.program mode l.input (values mode origin g node rule).rule (values mode origin g node rule).tape (values mode origin g node rule).fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have entry:=image.body.state.head.graph.entry
  have forward:=image.body.state.head.graph.forward
  have whole:=Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image
  have leading:=StringDwordWritesBridge.trace mode (Listing8MainPrefix.trace mode l t (values mode origin g node rule) b.state.head.input.input.prefixBounds state entry forward current.state.head.input.prefixCurrent)
  have short:=StringDwordWritesBridge.trace mode (Listing8MainInput.trace mode l t (values mode origin g node rule) old b.state.head.input state entry forward current.state.head.input)
  have localKept:=Listing8JointTemplateBindings.graph_input mode origin l t g node rule ctx old state image.body.state.head.graph
  have shape : ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))++
      (((Listing8LiteralComposition.program mode l.input (values mode origin g node rule).rule (values mode origin g node rule).tape (values mode origin g node rule).fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode))=
      (Listing8MainInput.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode) := by
    rw [Listing8MainInput.program,List.map_append]
  rw [←shape] at short
  have size : (((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))++
      (((Listing8LiteralComposition.program mode l.input (values mode origin g node rule).rule (values mode origin g node rule).tape (values mode origin g node rule).fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode))).length≤
      (Listing8LoopControl.program mode origin l t g node rule state).length := by
    rw [shape,List.length_map,Listing8MainInput.instruction_count,Listing8LoopControl.instruction_count]
    cases mode <;> decide
  exact StringTemplateTraceSegments.join_segment mode _ _ _ _ _ state _ _ _ size leading short whole.1 whole.2 localKept

/-- Global control and local executable validity refer to the same actual phase. -/
theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      ((∀ descriptor∈Listing8HeadTemplateFields.arithmetic mode (Listing8DirectionGeometry.region mode l), DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧ (∀ helper∈Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l), DwordXorTemplates.Decodes mode helper reached.principal.memory)))
      ((Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l) (Listing8LoopDirection.finish mode l t (values mode origin g node rule) state)).map (StringStoreWrites.liftDword mode))
      (Listing8LoopDirection.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have entry:=image.body.state.head.graph.entry
  have forward:=image.body.state.head.graph.forward
  have whole:=Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image
  have leading:=StringDwordWritesBridge.trace mode (Listing8LoopDirection.trace mode l t (values mode origin g node rule) old b.state.head state entry forward current.state.head)
  have short:=StringDwordWritesBridge.trace mode (Listing8LoopHead.trace mode l t (values mode origin g node rule) old b.state.head state entry forward current.state.head)
  have localKept:=Listing8HeadTemplateBindings.maintained mode l t (values mode origin g node rule) old b.state.head state entry forward current.state.head
  have shape : ((Listing8LoopDirection.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode))++
      ((Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l) (Listing8LoopDirection.finish mode l t (values mode origin g node rule) state)).map (StringStoreWrites.liftDword mode))=
      (Listing8LoopHead.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode) := by
    rw [Listing8LoopHead.program,List.map_append]
  rw [←shape] at short
  have size : (((Listing8LoopDirection.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode))++
      ((Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l) (Listing8LoopDirection.finish mode l t (values mode origin g node rule) state)).map (StringStoreWrites.liftDword mode))).length≤
      (Listing8LoopControl.program mode origin l t g node rule state).length := by
    rw [shape,List.length_map,Listing8LoopHead.instruction_count,Listing8LoopControl.instruction_count]
    cases mode <;> decide
  exact StringTemplateTraceSegments.join_segment mode _ _ _ _ _ state _ _ _ size leading short whole.1 whole.2 localKept

/-- Global control and local executable validity refer to the same actual phase. -/
theorem state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      ((∀ descriptor∈Listing8StateTemplateFields.arithmetic mode (Listing8StateGeometry.region mode l), DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧ (∀ descriptor∈Listing8StateTemplateFields.fixed mode (Listing8StateGeometry.region mode l), MixedFixedTemplates.Decodes mode descriptor reached.principal.memory)))
      ((Listing8StateTrace.program mode (Listing8StateGeometry.region mode l) (Listing8LoopHead.finish mode l t (values mode origin g node rule) state)).map (StringStoreWrites.liftDword mode))
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have entry:=image.body.state.head.graph.entry
  have forward:=image.body.state.head.graph.forward
  have whole:=Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image
  have leading:=StringDwordWritesBridge.trace mode (Listing8LoopHead.trace mode l t (values mode origin g node rule) old b.state.head state entry forward current.state.head)
  have short:=StringDwordWritesBridge.trace mode (Listing8LoopState.trace mode l t (values mode origin g node rule) old b.state state entry forward current.state)
  have localKept:=Listing8StateTemplateBindings.maintained mode l t (values mode origin g node rule) old b.state state entry forward current.state
  have shape : ((Listing8LoopHead.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode))++
      ((Listing8StateTrace.program mode (Listing8StateGeometry.region mode l) (Listing8LoopHead.finish mode l t (values mode origin g node rule) state)).map (StringStoreWrites.liftDword mode))=
      (Listing8LoopState.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode) := by
    rw [Listing8LoopState.program,List.map_append]
  rw [←shape] at short
  have size : (((Listing8LoopHead.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode))++
      ((Listing8StateTrace.program mode (Listing8StateGeometry.region mode l) (Listing8LoopHead.finish mode l t (values mode origin g node rule) state)).map (StringStoreWrites.liftDword mode))).length≤
      (Listing8LoopControl.program mode origin l t g node rule state).length := by
    rw [shape,List.length_map,Listing8LoopState.instruction_count,Listing8LoopControl.instruction_count]
    cases mode <;> decide
  exact StringTemplateTraceSegments.join_segment mode _ _ _ _ _ state _ _ _ size leading short whole.1 whole.2 localKept

/-- The live failure/CALL fields and global control decode at the same
actual failure-phase prefixes; all later packet states are derived. -/
theorem failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8FailureExecutableTemplates.Decodes mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) reached.principal.memory)
      ((Listing8FailureTrace.program mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8LoopState.finish mode l t (values mode origin g node rule) state)).map StringStack.Form.previous) (Listing8LoopState.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have entry:=image.body.state.head.graph.entry
  have forward:=image.body.state.head.graph.forward
  have whole:=Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image
  have leading:=StringDwordWritesBridge.trace mode (Listing8LoopState.trace mode l t (values mode origin g node rule) old b.state state entry forward current.state)
  have short:=StringStack.previous_trace mode (Listing8LoopFailure.trace mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state entry forward current)
  have localKept:=Listing8FailureTemplateBindings.maintained mode origin l t g node rule ctx old state image
  have shape : ((Listing8LoopState.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode))++((Listing8FailureTrace.program mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8LoopState.finish mode l t (values mode origin g node rule) state)).map StringStack.Form.previous)=
      (Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous := by
    rw [Listing8LoopFailure.program,List.map_append,Listing8GlobalLoopMainRegions.lift_dword]
  rw [←shape] at short
  have size : (((Listing8LoopState.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode))++((Listing8FailureTrace.program mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8LoopState.finish mode l t (values mode origin g node rule) state)).map StringStack.Form.previous)).length≤
      (Listing8LoopControl.program mode origin l t g node rule state).length := by
    rw [shape,List.length_map,Listing8LoopFailure.instruction_count,Listing8LoopControl.instruction_count]
    cases mode <;> decide
  exact StringTemplateTraceSegments.join_segment mode _ _ _ _ _ state _ _ _ size leading short whole.1 whole.2 localKept

end SmcTuring.Appendix.Listing8MaintainedJointPhases

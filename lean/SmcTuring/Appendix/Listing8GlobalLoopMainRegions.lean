module
public import SmcTuring.Appendix.Listing8GlobalMainPrefixRegions
public import SmcTuring.Appendix.Listing8GlobalInputRegions
public import SmcTuring.Appendix.Listing8GlobalSelectionRegions
public import SmcTuring.Appendix.Listing8GlobalFailureRegions

public section
namespace SmcTuring.Appendix.Listing8GlobalLoopMainRegions
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem lift_dword (mode : Mode) (forms : List (StringDword.Form mode)) :
    (forms.map StringControl.Form.previous).map StringStack.Form.previous=forms.map (StringStoreWrites.liftDword mode) := by
  rw [List.map_map];rfl

theorem input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8MainInput.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have trace:=StringDwordWritesBridge.trace mode (Listing8MainPrefix.trace mode l t _
    (Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds state current.entry current.forward image.prefixCurrent)
  rw [Listing8MainInput.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  exact ⟨Listing8GlobalMainPrefixRegions.regions mode origin l t g node rule ctx state current.entry current.forward image.prefixCurrent,
    Listing8GlobalInputRegions.regions mode origin l t g node rule ctx old state current⟩

theorem direction (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8LoopDirection.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode)) state := by
  have bounds:=Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have trace:=(Listing8MainInputWrites.execute mode origin l t g node rule ctx old state current.graph).1
  rw [Listing8LoopDirection.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  exact ⟨input mode origin l t g node rule ctx old state current.graph,
    Listing8GlobalSelectionRegions.direction mode origin l t g node rule ctx _
      (Listing8MainInput.endpoint mode l t _ old bounds.input state current.graph.entry current.graph.forward image.input)⟩

theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8LoopHead.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode)) state := by
  have bounds:=Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have trace:=StringDwordWritesBridge.trace mode (Listing8LoopDirection.trace mode l t _ old bounds state current.graph.entry current.graph.forward image)
  rw [Listing8LoopHead.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  exact ⟨direction mode origin l t g node rule ctx old state current,
    Listing8GlobalSelectionRegions.head mode origin l t g node rule ctx _
      (Listing8LoopDirection.endpoint mode l t _ old bounds state current.graph.entry current.graph.forward image)⟩

theorem state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (machine : StringExecution.State mode)
    (current : Listing8LoopGraphState.Current mode origin l t g node rule old machine) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8LoopState.program mode l t (values mode origin g node rule) machine).map (StringStoreWrites.liftDword mode)) machine := by
  have bounds:=Listing8LoopGraphState.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphState.input_current mode origin l t g node rule old machine ctx.nodeLocated ctx.ruleLocated current
  have trace:=(Listing8LoopHeadWrites.execute mode origin l t g node rule ctx old machine current.head).1
  rw [Listing8LoopState.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  exact ⟨head mode origin l t g node rule ctx old machine current.head,
    Listing8GlobalSelectionRegions.state mode origin l t g node rule ctx _
      (Listing8LoopHead.endpoint mode l t _ old bounds.head machine current.head.graph.entry current.head.graph.forward image.head)⟩

set_option maxHeartbeats 800000 in
theorem failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (machine : StringExecution.State mode)
    (current : Listing8LoopGraphFailure.Current mode origin l t g node rule old machine) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8BootImage.beginPC mode origin) machine).map StringStack.Form.previous) machine := by
  have bounds:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old machine ctx.nodeLocated ctx.ruleLocated current
  have trace:=StringDwordWritesBridge.trace mode (Listing8LoopState.trace mode l t _ old bounds.state machine
    current.state.head.graph.entry current.state.head.graph.forward image.state)
  rw [Listing8LoopFailure.program,List.map_append,lift_dword,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  exact ⟨state mode origin l t g node rule ctx old machine current.state,
    Listing8GlobalFailureRegions.regions mode origin _ (Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx)
      (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
      (Listing8LoopState.endpoint mode l t _ old bounds.state machine current.state.head.graph.entry current.state.head.graph.forward image.state)
      (Listing8LoopFailurePrefix.current_after_state mode l t _ old _ _ bounds machine
        current.state.head.graph.entry current.state.head.graph.forward image)⟩

end SmcTuring.Appendix.Listing8GlobalLoopMainRegions

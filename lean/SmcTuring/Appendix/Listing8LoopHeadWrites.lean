module
public import SmcTuring.Appendix.Listing8MainInputWrites
public import SmcTuring.Appendix.Listing8LoopGraphHead
public import SmcTuring.Appendix.Listing8GraphHeadWrites

public section
namespace SmcTuring.Appendix.Listing8LoopHeadWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets := Listing8PointerCopies.Targets
abbrev OldInput := Listing8MainInput.OldInput
abbrev Current := Listing8LoopGraphHead.Current

theorem direction_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8LoopDirection.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode)) state := by
  have bounds := Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image := Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  rw [Listing8LoopDirection.program,List.map_append]
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ state (Listing8MainInput.finish mode l t (values mode origin g node rule) state)
  · exact (Listing8MainInputWrites.execute mode origin l t g node rule ctx old state current.graph).1
  · exact Listing8MainInputWrites.owned mode origin l t g node rule ctx old state current.graph
  · exact Listing8DirectionWrites.owned mode origin _ (Listing8DirectionGeometry.region mode l)
      (Listing8GraphDirectionWrites.region_bounds mode origin l t g node rule ctx) ctx.body.state.head.capacity _
      (Listing8MainInput.endpoint mode l t _ old bounds.input state current.graph.entry current.graph.forward image.input)

/-- All head-selection packet values and entry PCs come from the actual
repeated prefix/input/direction run. Full cursor width lies inside code. -/
theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8LoopHead.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode)) state := by
  have bounds := Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image := Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  rw [Listing8LoopHead.program,List.map_append]
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ state (Listing8LoopDirection.finish mode l t (values mode origin g node rule) state)
  · exact StringDwordWritesBridge.trace mode (Listing8LoopDirection.trace mode l t _ old bounds
      state current.graph.entry current.graph.forward image)
  · exact direction_owned mode origin l t g node rule ctx old state current
  · exact Listing8HeadTailWrites.owned mode origin _ (Listing8DirectionGeometry.region mode l)
      (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head)
      (Listing8GraphDirectionWrites.region_bounds mode origin l t g node rule ctx)
      (Listing8GraphInputWriteBounds.cursor_tape mode origin l t g node rule ctx).1 _
      (Listing8LoopDirection.endpoint mode l t _ old bounds state current.graph.entry current.graph.forward image)

theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      ((Listing8LoopHead.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode))
      (Listing8LoopHead.finish mode l t (values mode origin g node rule) state) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8LoopHead.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode)) state :=
  ⟨StringDwordWritesBridge.trace mode (Listing8LoopHead.trace mode l t _ old
      (Listing8LoopGraphHead.bounds mode origin l t g node rule ctx) state current.graph.entry current.graph.forward
      (Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current)),
    owned mode origin l t g node rule ctx old state current⟩

end SmcTuring.Appendix.Listing8LoopHeadWrites

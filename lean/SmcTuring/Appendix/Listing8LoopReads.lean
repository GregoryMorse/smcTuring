module
public import SmcTuring.Appendix.Listing8MainReads
public import SmcTuring.Appendix.Listing8TailReadClasses

public section
namespace SmcTuring.Appendix.Listing8LoopReads
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

theorem direction (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      ((Listing8LoopDirection.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode)) state := by
  have first:=(Listing8MainInputWrites.execute mode origin l t g node rule ctx old state current.graph).1
  have owned:=Listing8LoopHeadWrites.direction_owned mode origin l t g node rule ctx old state current
  rw [Listing8LoopDirection.program,List.map_append,StringWrites.owned_run_append,StringWrites.trace_run_eq mode first] at owned
  rw [Listing8LoopDirection.program,List.map_append]
  exact StringReadRuns.append_trace mode _ _ _ state _ first
    (Listing8MainReads.input mode origin l t g node rule ctx old state current.graph)
    (StringReadRuns.local_of_owned mode origin _ _ _ (Listing8TailReadClasses.direction mode _ _) owned.2)

theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopGraphHead.Current mode origin l t g node rule old state) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      ((Listing8LoopHead.program mode l t (values mode origin g node rule) state).map (StringStoreWrites.liftDword mode)) state := by
  have bounds:=Listing8LoopGraphHead.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphHead.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have first:=StringDwordWritesBridge.trace mode (Listing8LoopDirection.trace mode l t _ old bounds
    state current.graph.entry current.graph.forward image)
  have owned:=Listing8LoopHeadWrites.owned mode origin l t g node rule ctx old state current
  rw [Listing8LoopHead.program,List.map_append,StringWrites.owned_run_append,StringWrites.trace_run_eq mode first] at owned
  rw [Listing8LoopHead.program,List.map_append]
  exact StringReadRuns.append_trace mode _ _ _ state _ first (direction mode origin l t g node rule ctx old state current)
    (StringReadRuns.local_of_owned mode origin _ _ _ (Listing8TailReadClasses.head mode _ _) owned.2)

theorem state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (seed : StringExecution.State mode)
    (current : Listing8LoopGraphState.Current mode origin l t g node rule old seed) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      ((Listing8LoopState.program mode l t (values mode origin g node rule) seed).map (StringStoreWrites.liftDword mode)) seed := by
  have first:=(Listing8LoopHeadWrites.execute mode origin l t g node rule ctx old seed current.head).1
  have owned:=Listing8LoopStateWrites.owned mode origin l t g node rule ctx old seed current
  rw [Listing8LoopState.program,List.map_append,StringWrites.owned_run_append,StringWrites.trace_run_eq mode first] at owned
  rw [Listing8LoopState.program,List.map_append]
  exact StringReadRuns.append_trace mode _ _ _ seed _ first (head mode origin l t g node rule ctx old seed current.head)
    (StringReadRuns.local_of_owned mode origin _ _ _ (Listing8TailReadClasses.state mode _ _) owned.2)

theorem failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (seed : StringExecution.State mode)
    (current : Listing8LoopGraphFailure.Current mode origin l t g node rule old seed) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      ((Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8BootImage.beginPC mode origin) seed).map StringStack.Form.previous) seed := by
  have first:=(Listing8LoopStateWrites.execute mode origin l t g node rule ctx old seed current.state).1
  rw [Listing8LoopFailure.program,List.map_append,List.map_map]
  change StringReadRuns.Run mode _
    (((Listing8LoopState.program mode l t (values mode origin g node rule) seed).map (StringStoreWrites.liftDword mode))++_) seed
  exact StringReadRuns.append_trace mode _ _ _ seed _ first (state mode origin l t g node rule ctx old seed current.state)
    (StringReadRuns.local_of_owned mode origin _ _ _ (Listing8TailReadClasses.failure mode _ _)
      (Listing8LoopFailureWrites.failure_owned mode origin l t g node rule ctx old seed current))

/-- All data reads in one complete actual repeated iteration, including
both copy sources, head/state selection, fail-mask and CALL/return/reset,
are derived from the same present maintained entry and static Context. -/
theorem control (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (seed : StringExecution.State mode)
    (current : Listing8LoopControl.Current mode origin l t g node rule old seed) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8LoopControl.program mode origin l t g node rule seed) seed := by
  have first:=(Listing8LoopFailureWrites.execute mode origin l t g node rule ctx old seed current.body).1
  rw [Listing8LoopControl.program]
  exact StringReadRuns.append_trace mode _ _ _ seed _ first (failure mode origin l t g node rule ctx old seed current.body)
    (StringReadRuns.local_of_owned mode origin _ _ _ (Listing8TailReadClasses.jump_return mode origin _)
      (Listing8LoopReturnWrites.owned mode origin l t g node rule ctx old seed current))

end SmcTuring.Appendix.Listing8LoopReads

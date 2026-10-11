module
public import SmcTuring.Appendix.Listing8NativeHeadBoundary
public import SmcTuring.Appendix.Listing8LoopOriginalInterpreter

public section
namespace SmcTuring.Appendix.Listing8OriginalNativeHead
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets

theorem original_body (mode : Mode) (origin : Nat) (lower : Int) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (boundary : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) code boundary ∧
      Listing8NativeHeadBoundary.observe mode origin lower g.transitions l.input.cursor boundary.principal.memory=
        lower+((Listing8GraphStep.nextNode g node rule).val : Int) := by
  have actual:=Listing8GlobalBoot.trace mode origin l t (values mode origin g node rule) _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
    (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed
  have pointer:=Listing8GlobalBootValues.head mode origin l t (values mode origin g node rule) _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body
    (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed (g.rules rule).takeBack rfl
  rw [ctx.nodeLocated,Listing8GraphStep.head_pointer] at pointer
  have capacity:=Listing8GraphPointers.node_capacity mode origin g (Listing8GraphStep.nextNode g node rule) ctx.native
  exact ⟨_,_,actual,Listing8NativeHeadBoundary.pointer_position mode origin lower g _ l.input.cursor _ (by omega) pointer⟩

/-- Original initialization and every selected iteration construct the
reached head-observation boundary, including an immediate original halt. -/
theorem original_graph (mode : Mode) (origin : Nat) (lower : Int) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (cursor : Nat) (boundary : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) code boundary ∧
      Listing8NativeHeadBoundary.observe mode origin lower lastGraph.transitions cursor boundary.principal.memory=
        lower+((Listing8GraphStep.nextNode lastGraph lastNode lastRule).val : Int) := by
  cases logical with
  | refl =>
    obtain ⟨boundary,code,actual,head⟩:=original_body mode origin lower l t g node rule ctx memory seed
    exact ⟨l.input.cursor,boundary,code,actual,head⟩
  | @next g node rule target count lastGraph lastNode lastRule selected rest =>
    have nonhalt : ¬Listing8GraphRun.Halted g node rule := by
      intro stopped
      have absent:=(Listing8GraphStep.halted_iff g node rule).mpr stopped
      rw [selected] at absent
      cases absent
    have first:=Listing8GraphBackedge.trace mode origin l t g node rule ctx memory seed nonhalt
    obtain ⟨cursor,boundary,finalState,before,after,reached,tail,whole,head⟩:=
      Listing8NativeHeadBoundary.iterations mode origin lower t rest halted (nextLayout mode origin l g node rule target)
        (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
        (Listing8LoopGraphContext.next mode origin l t g node rule target ctx)
        (Listing8LoopHaltImage.after_backedge mode origin l t g node rule target ctx selected memory seed)
    exact ⟨cursor,boundary,_,StringStack.trace_append mode first reached,head⟩

end SmcTuring.Appendix.Listing8OriginalNativeHead

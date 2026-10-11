module
public import SmcTuring.Appendix.Listing8LoopHaltImage
public import SmcTuring.Appendix.Listing8LoopIteration
public import SmcTuring.Appendix.Listing8LoopIterationWrites
public import SmcTuring.Appendix.Listing8LoopReads
public import SmcTuring.Appendix.Listing8LoopControlFetch

public section
namespace SmcTuring.Appendix.Listing8LoopIterationFetch
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run StringFetchWindows.Run

/-- Finite native iteration with every actual classifier/fetch and data-read window and the complete main-entry invariant preserved.
The native trace is derived by induction from logical steps and actual code;
no future packet, readiness, state or native trace is an input. -/
theorem execute (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (l : Layout) (oldInput : OldInput) (state : StringExecution.State mode)
    (ctx : Context mode origin l t g node rule) (image : Listing8LoopHaltImage.Current mode origin l t g node rule oldInput state) :
    ∃ (lastLayout : Layout) (lastOld : OldInput) (lastState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      Context mode origin lastLayout t lastGraph lastNode lastRule ∧
      Listing8LoopHaltImage.Current mode origin lastLayout t lastGraph lastNode lastRule lastOld lastState ∧
      StringStack.Trace mode state code lastState ∧
      StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) code state ∧
      StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ code state ∧ StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ code state ∧ code.length=count*(if mode=.x86 then 139 else 182) ∧
      lastState.principal.stack=state.principal.stack ∧ lastState.sourceIndex=state.sourceIndex ∧ lastState.destinationIndex=state.destinationIndex := by
  induction logical generalizing l oldInput state with
  | refl =>
    exact ⟨l,oldInput,state,[],ctx,image,StringStack.Trace.nil _,by simp only [StringWrites.OwnedRun],by simp only [StringReadRuns.Run],by simp only [StringFetchWindows.Run],by simp only [List.length_nil,Nat.zero_mul],rfl,rfl,rfl⟩
  | @next g node rule target count lastGraph lastNode lastRule selected rest ih =>
    let nextState:=Listing8LoopControl.finish mode origin l t g node rule state
    let nextOld:=Listing8LoopControlReentryFields.old mode origin g node rule
    let nextL:=nextLayout mode origin l g node rule target
    have nextCtx:=Listing8LoopGraphContext.next mode origin l t g node rule target ctx
    have nextImage:=Listing8LoopHaltImage.reentry mode origin l t g node rule ctx oldInput state image target selected
    obtain ⟨lastL,lastOld,lastState,tail,lastCtx,lastImage,lastTrace,tailOwned,tailReads,tailFetch,lastLength,stack,source,destination⟩:=ih nextL nextOld nextState nextCtx nextImage
    rw [show (Listing8GraphStep.updated g node rule).transitions=g.transitions from rfl,
      show (Listing8GraphStep.updated g node rule).nodes=g.nodes from rfl] at tailOwned tailReads tailFetch
    have first:=Listing8LoopControl.trace mode origin l t g node rule ctx oldInput state image.control
    have registers:=Listing8LoopControl.registers mode origin l t g node rule ctx oldInput state image.control
    have firstLength:=Listing8LoopControl.instruction_count mode origin l t g node rule state
    refine ⟨lastL,lastOld,lastState,Listing8LoopControl.program mode origin l t g node rule state++tail,
      lastCtx,lastImage,StringStack.trace_append mode first lastTrace,?_,?_,?_,?_,stack.trans registers.1,
      source.trans registers.2.1,destination.trans registers.2.2.1⟩
    · with_reducible
        exact StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
          (Listing8LoopControl.program mode origin l t g node rule state) tail state nextState first
          (Listing8LoopControlWrites.owned mode origin l t g node rule ctx oldInput state image.control) tailOwned
    · exact StringReadRuns.append_trace mode _ _ _ state nextState first
        (Listing8LoopReads.control mode origin l t g node rule ctx oldInput state image.control) tailReads
    · exact StringFetchWindows.append_trace mode _ _ _ state nextState first
        (Listing8LoopControlFetch.contained mode origin l t g node rule ctx oldInput state image.control) tailFetch
    · rw [List.length_append,firstLength,lastLength,Nat.add_mul,Nat.one_mul]
      omega


end SmcTuring.Appendix.Listing8LoopIterationFetch

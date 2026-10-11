module
public import SmcTuring.Appendix.Listing8LoopReentry

public section
namespace SmcTuring.Appendix.Listing8LoopIteration
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

/-- Logical rule/head/tape evolution alone. Each selected successor follows
from the current declared rule and symbol; native states and traces are absent. -/
inductive Steps : (g : Graph) → Fin g.nodes → Fin g.transitions → Nat →
    (lastGraph : Graph) → Fin lastGraph.nodes → Fin lastGraph.transitions → Prop where
  | refl (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) : Steps g node rule 0 g node rule
  | next {g : Graph} {node : Fin g.nodes} {rule target : Fin g.transitions} {count : Nat}
      {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
      (selected : Listing8GraphStep.nextRule g node rule=some target)
      (rest : Steps (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target count lastGraph lastNode lastRule) :
      Steps g node rule (count+1) lastGraph lastNode lastRule

/-- Finite native iteration with the complete main-entry invariant preserved.
The native trace is derived by induction from logical steps and actual code;
no future packet, readiness, state or native trace is an input. -/
theorem execute (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Steps g node rule count lastGraph lastNode lastRule)
    (l : Layout) (oldInput : OldInput) (state : StringExecution.State mode)
    (ctx : Context mode origin l t g node rule) (image : Listing8LoopControl.Current mode origin l t g node rule oldInput state) :
    ∃ (lastLayout : Layout) (lastOld : OldInput) (lastState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      Context mode origin lastLayout t lastGraph lastNode lastRule ∧
      Listing8LoopControl.Current mode origin lastLayout t lastGraph lastNode lastRule lastOld lastState ∧
      StringStack.Trace mode state code lastState ∧ code.length=count*(if mode=.x86 then 139 else 182) ∧
      lastState.principal.stack=state.principal.stack ∧ lastState.sourceIndex=state.sourceIndex ∧ lastState.destinationIndex=state.destinationIndex := by
  induction logical generalizing l oldInput state with
  | refl =>
    exact ⟨l,oldInput,state,[],ctx,image,StringStack.Trace.nil _,by simp only [List.length_nil,Nat.zero_mul],rfl,rfl,rfl⟩
  | @next g node rule target count lastGraph lastNode lastRule selected rest ih =>
    let nextState:=Listing8LoopControl.finish mode origin l t g node rule state
    let nextOld:=Listing8LoopControlReentryFields.old mode origin g node rule
    let nextL:=nextLayout mode origin l g node rule target
    have nextCtx:=Listing8LoopGraphContext.next mode origin l t g node rule target ctx
    have nextImage:=Listing8LoopReentry.current mode origin l t g node rule ctx oldInput state image target selected
    obtain ⟨lastL,lastOld,lastState,tail,lastCtx,lastImage,lastTrace,lastLength,stack,source,destination⟩:=ih nextL nextOld nextState nextCtx nextImage
    have first:=Listing8LoopControl.trace mode origin l t g node rule ctx oldInput state image
    have registers:=Listing8LoopControl.registers mode origin l t g node rule ctx oldInput state image
    have firstLength:=Listing8LoopControl.instruction_count mode origin l t g node rule state
    refine ⟨lastL,lastOld,lastState,Listing8LoopControl.program mode origin l t g node rule state++tail,
      lastCtx,lastImage,StringStack.trace_append mode first lastTrace,?_,stack.trans registers.1,
      source.trans registers.2.1,destination.trans registers.2.2.1⟩
    rw [List.length_append,firstLength,lastLength,Nat.add_mul,Nat.one_mul]
    omega

end SmcTuring.Appendix.Listing8LoopIteration

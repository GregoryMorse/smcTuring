module
public import SmcTuring.Appendix.Listing8GlobalMainControlTemplates
public import SmcTuring.Appendix.Listing8LoopIteration

public section
namespace SmcTuring.Appendix.Listing8GlobalIterationTemplates
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

/-- Logical steps construct all maintained iterations and their subsequent
entry images. Both targets, the stack prefix, live CALL and early declarations
decode jointly at every native prefix of this entire finite continuation. -/
theorem execute (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (l : Layout) (oldInput : OldInput) (state : StringExecution.State mode)
    (ctx : Context mode origin l t g node rule)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule oldInput state) :
    ∃ (lastLayout : Layout) (lastOld : OldInput) (lastState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      Context mode origin lastLayout t lastGraph lastNode lastRule ∧
      Listing8LoopHaltImage.Current mode origin lastLayout t lastGraph lastNode lastRule lastOld lastState ∧
      StringStack.Trace mode state code lastState ∧
      StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory) code state ∧
      code.length=count*(if mode=.x86 then 139 else 182) := by
  induction logical generalizing l oldInput state with
  | refl g node rule =>
    have catalog:=(Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx oldInput state image.control).2
    have initial:=StringTemplateStates.at_prefix mode
      (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      [] (Listing8LoopControl.program mode origin l t g node rule state) state catalog
    have empty : StringTemplateStates.Run mode
        (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory) [] state := by
      rw [StringTemplateStates.Run]
      exact initial
    exact ⟨l,oldInput,state,[],ctx,image,StringStack.Trace.nil _,empty,by simp only [List.length_nil,Nat.zero_mul]⟩
  | @next g node rule target count lastGraph lastNode lastRule selected rest ih =>
    let nextState:=Listing8LoopControl.finish mode origin l t g node rule state
    let nextOld:=Listing8LoopControlReentryFields.old mode origin g node rule
    let nextL:=nextLayout mode origin l g node rule target
    have nextCtx:=Listing8LoopGraphContext.next mode origin l t g node rule target ctx
    have nextImage:=Listing8LoopHaltImage.reentry mode origin l t g node rule ctx oldInput state image target selected
    obtain ⟨lastL,lastOld,lastState,tail,lastCtx,lastImage,lastTrace,tailTemplates,lastLength⟩:=
      ih nextL nextOld nextState nextCtx nextImage
    have first:=Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx oldInput state image.control
    refine ⟨lastL,lastOld,lastState,Listing8LoopControl.program mode origin l t g node rule state++tail,
      lastCtx,lastImage,StringStack.trace_append mode first.1 lastTrace,?_,?_⟩
    · rw [StringTemplateStates.append,StringWrites.trace_run_eq mode first.1]
      exact ⟨first.2,tailTemplates⟩
    · rw [List.length_append,Listing8LoopControl.instruction_count,lastLength,Nat.add_mul,Nat.one_mul]
      omega

end SmcTuring.Appendix.Listing8GlobalIterationTemplates

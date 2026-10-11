module
public import SmcTuring.Appendix.Listing8BoundarySummary
public import SmcTuring.Appendix.Listing8LoopHaltIteration

public section
namespace SmcTuring.Appendix.Listing8JointIteration
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
set_option maxHeartbeats 2000000

/-- Constructed phase certificates for the actual appended maintained passes.
The graph/entry of each later pass is the executed previous exit. -/
inductive Run (mode : Mode) (origin : Nat) (t : Targets) :
    (g : Graph) → Fin g.nodes → Fin g.transitions → Layout → OldInput → StringExecution.State mode →
    (lastGraph : Graph) → Fin lastGraph.nodes → Fin lastGraph.transitions → Layout → OldInput → StringExecution.State mode →
    List (StringStack.Form mode) → Prop where
  | nil {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {l : Layout} {old : OldInput} {state : StringExecution.State mode}
      (ctx : Context mode origin l t g node rule) (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state) :
      Run mode origin t g node rule l old state g node rule l old state []
  | step {g : Graph} {node : Fin g.nodes} {rule target : Fin g.transitions} {l : Layout} {old : OldInput} {state : StringExecution.State mode}
      {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
      {lastL : Layout} {lastOld : OldInput} {lastState : StringExecution.State mode} {code : List (StringStack.Form mode)}
      (ctx : Context mode origin l t g node rule) (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
      (selected : Listing8GraphStep.nextRule g node rule=some target)
      (prefixes : ∀ before after,Listing8LoopControl.program mode origin l t g node rule state=before++after →
        Listing8JointCopyOwnerLifetimes.PrefixInvariant mode origin l t g node rule state before (StringWrites.run mode before state))
      (later : Run mode origin t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
        (nextLayout mode origin l g node rule target) (Listing8LoopControlReentryFields.old mode origin g node rule)
        (Listing8LoopControl.finish mode origin l t g node rule state) lastGraph lastNode lastRule lastL lastOld lastState code) :
      Run mode origin t g node rule l old state lastGraph lastNode lastRule lastL lastOld lastState
        (Listing8LoopControl.program mode origin l t g node rule state++code)

/-- Every witness is anchored to the SAME whole-run prefix and the exact
current graph/layout of its phase. The accepted main invariant is retained. -/
@[expose] def PrefixWitness (mode : Mode) (origin : Nat) (t : Targets) (initial : StringExecution.State mode)
    (before : List (StringStack.Form mode)) (reached : StringExecution.State mode) :=
  ∃ (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (l : Layout) (old : OldInput)
    (state : StringExecution.State mode) (leading localForms rest : List (StringStack.Form mode)),
    Context mode origin l t g node rule ∧ Listing8LoopHaltImage.Current mode origin l t g node rule old state ∧
    Listing8LoopControl.program mode origin l t g node rule state=localForms++rest ∧
    before=leading++localForms ∧ state=StringWrites.run mode leading initial ∧
    reached=StringWrites.run mode localForms state ∧
    Listing8JointCopyOwnerLifetimes.PrefixInvariant mode origin l t g node rule state localForms reached

theorem trace (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {l : Layout} {old : OldInput} {state : StringExecution.State mode}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    {lastL : Layout} {lastOld : OldInput} {lastState : StringExecution.State mode} {code : List (StringStack.Form mode)}
    (all : Run mode origin t g node rule l old state lastGraph lastNode lastRule lastL lastOld lastState code) :
    StringStack.Trace mode state code lastState := by
  induction all with
  | nil => exact .nil _
  | step ctx image _ _ _ ih =>
    exact StringStack.trace_append mode
      (Listing8LoopControl.trace mode origin _ t _ _ _ ctx _ _ image.control) ih

/-- The joint certificate is OUTPUT of induction on logical source steps.
No whole-run trace,catalog or future image is an input. -/
theorem execute (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (l : Layout) (oldInput : OldInput) (state : StringExecution.State mode)
    (ctx : Context mode origin l t g node rule) (image : Listing8LoopHaltImage.Current mode origin l t g node rule oldInput state) :
    ∃ (lastL : Layout) (lastOld : OldInput) (lastState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      Context mode origin lastL t lastGraph lastNode lastRule ∧
      Listing8LoopHaltImage.Current mode origin lastL t lastGraph lastNode lastRule lastOld lastState ∧
      Run mode origin t g node rule l oldInput state lastGraph lastNode lastRule lastL lastOld lastState code ∧
      StringStack.Trace mode state code lastState ∧ code.length=count*(if mode=.x86 then 139 else 182) := by
  induction logical generalizing l oldInput state with
  | refl => exact ⟨l,oldInput,state,[],ctx,image,Run.nil ctx image,.nil _,by simp⟩
  | @next g node rule target count lastGraph lastNode lastRule selected rest ih =>
    let nextState := Listing8LoopControl.finish mode origin l t g node rule state
    let nextOld := Listing8LoopControlReentryFields.old mode origin g node rule
    let nextL := nextLayout mode origin l g node rule target
    have nextCtx := Listing8LoopGraphContext.next mode origin l t g node rule target ctx
    have nextImage := Listing8LoopHaltImage.reentry mode origin l t g node rule ctx oldInput state image target selected
    obtain ⟨lastL,lastOld,lastState,tail,lastCtx,lastImage,later,lastTrace,lastLength⟩ := ih nextL nextOld nextState nextCtx nextImage
    have joint := Run.step ctx image selected
      (Listing8JointCopyOwnerLifetimes.complete mode origin l t g node rule ctx oldInput state image.control) later
    refine ⟨lastL,lastOld,lastState,Listing8LoopControl.program mode origin l t g node rule state++tail,
      lastCtx,lastImage,joint,trace mode origin t joint,?_⟩
    rw [List.length_append,Listing8LoopControl.instruction_count,lastLength,Nat.add_mul,Nat.one_mul]
    omega

/-- Every actual prefix of the inductively composed run has one same-prefix
joint catalog witness,including initial and final reentry boundaries. -/
theorem at_prefix (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {l : Layout} {old : OldInput} {state : StringExecution.State mode}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    {lastL : Layout} {lastOld : OldInput} {lastState : StringExecution.State mode} {code : List (StringStack.Form mode)}
    (all : Run mode origin t g node rule l old state lastGraph lastNode lastRule lastL lastOld lastState code)
    (before after : List (StringStack.Form mode)) (cut : code=before++after) :
    PrefixWitness mode origin t state before (StringWrites.run mode before state) := by
  induction all generalizing before after with
  | @nil g node rule l old state ctx image =>
    cases before with
    | nil => exact ⟨g,node,rule,l,old,state,[],[],Listing8LoopControl.program mode origin l t g node rule state,
        ctx,image,rfl,rfl,rfl,rfl,Listing8JointCopyOwnerLifetimes.complete mode origin l t g node rule ctx old state image.control [] _ rfl⟩
    | cons => cases cut
  | @step g node rule target l old state lastGraph lastNode lastRule lastL lastOld lastState code ctx image selected prefixes later ih =>
    rcases Listing8BoundarySummary.cut_append (Listing8LoopControl.program mode origin l t g node rule state) code before after cut with
      ⟨rest,split⟩ | ⟨pre,rest,split,location⟩
    · exact ⟨g,node,rule,l,old,state,[],before,rest,ctx,image,split,rfl,rfl,rfl,prefixes before rest split⟩
    · have actual := StringWrites.trace_run_eq mode (Listing8LoopControl.trace mode origin l t g node rule ctx old state image.control)
      have reached : StringWrites.run mode before state=StringWrites.run mode pre (Listing8LoopControl.finish mode origin l t g node rule state) := by
        rw [location,StringWrites.run_append,actual]
      rw [reached]
      obtain ⟨nextG,nextNode,nextRule,nextL,nextOld,nextState,lead,part,last,nextCtx,nextImage,localCut,localLocation,localEntry,localReached,localCatalog⟩ := ih pre rest split
      refine ⟨nextG,nextNode,nextRule,nextL,nextOld,nextState,Listing8LoopControl.program mode origin l t g node rule state++lead,part,last,
        nextCtx,nextImage,localCut,?_,?_,localReached,localCatalog⟩
      · rw [location,localLocation,List.append_assoc]
      · rw [StringWrites.run_append,actual]
        exact localEntry

end SmcTuring.Appendix.Listing8JointIteration

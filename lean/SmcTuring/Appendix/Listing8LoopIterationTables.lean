module
public import SmcTuring.Appendix.Listing8LoopIterationAnchor

public section
namespace SmcTuring.Appendix.Listing8LoopIterationTables
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem table_bytes {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (mode : Mode) (origin start : Nat) :
    Listing8TransitionTable.bytes mode start (table mode origin lastGraph)=Listing8TransitionTable.bytes mode start (table mode origin g) := by
  induction logical with
  | refl => rfl
  | @next g node rule target count lastGraph lastNode lastRule selected rest ih =>
    exact ih.trans (Listing8MainGraphTable.updated_table_bytes mode origin g node rule start)

/-- The native finite-iteration endpoint retains the original rule bytes,
including every declaration. The reached image is constructed by execute. -/
theorem execute (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (l : Layout) (oldInput : OldInput) (state : StringExecution.State mode)
    (ctx : Context mode origin l t g node rule) (image : Listing8LoopControl.Current mode origin l t g node rule oldInput state) :
    ∃ (lastLayout : Layout) (lastOld : OldInput) (lastState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      Context mode origin lastLayout t lastGraph lastNode lastRule ∧
      Listing8LoopControl.Current mode origin lastLayout t lastGraph lastNode lastRule lastOld lastState ∧
      StringStack.Trace mode state code lastState ∧ code.length=count*(if mode=.x86 then 139 else 182) ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) lastState.principal.memory := by
  obtain ⟨lastL,lastOld,lastState,code,lastCtx,lastImage,actual,length,stack,source,destination⟩:=
    Listing8LoopIteration.execute mode origin t logical l oldInput state ctx image
  refine ⟨lastL,lastOld,lastState,code,lastCtx,lastImage,actual,length,?_⟩
  have original:=lastImage.body.state.head.graph.rules
  rw [Listing8TransitionTable.Initial,table_bytes logical mode origin (Listing8FullTableImage.start mode origin)] at original
  exact original

/-- One original initialization, its first body/return and any finite
logical continuation preserve the entire original transition table. -/
theorem original_execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    {count : Nat} {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target count lastGraph lastNode lastRule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (lastLayout : Layout) (lastOld : OldInput) (lastState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      Context mode origin lastLayout t lastGraph lastNode lastRule ∧
      Listing8LoopControl.Current mode origin lastLayout t lastGraph lastNode lastRule lastOld lastState ∧
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) code lastState ∧
      code.length=(if mode=.x86 then 147 else 195)+count*(if mode=.x86 then 139 else 182) ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) lastState.principal.memory := by
  obtain ⟨lastL,lastOld,lastState,code,lastCtx,lastImage,actual,length,stack,source,destination⟩:=
    Listing8LoopIterationAnchor.execute mode origin l t g node rule target ctx selected logical memory seed
  refine ⟨lastL,lastOld,lastState,code,lastCtx,lastImage,actual,length,?_⟩
  have original:=lastImage.body.state.head.graph.rules
  rw [Listing8TransitionTable.Initial,table_bytes (Listing8LoopIteration.Steps.next selected logical) mode origin (Listing8FullTableImage.start mode origin)] at original
  exact original

end SmcTuring.Appendix.Listing8LoopIterationTables

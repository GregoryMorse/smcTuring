module
public import SmcTuring.Appendix.Listing8JointIteration
public import SmcTuring.Appendix.Listing8LoopInterpreter
public import SmcTuring.Appendix.Listing9TMStaticExecution
public import SmcTuring.Appendix.Listing9PackedCapacity
public import SmcTuring.Appendix.Listing8TMObservedRun

public section
namespace SmcTuring.Appendix.Listing8JointInterpreter
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
set_option maxHeartbeats 2000000

@[expose] def tail (mode : Mode) (origin : Nat) (l : Layout) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) :=
  (Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map (StringStoreWrites.liftDword mode)++
  (Listing8ResetLayout.program mode (Listing8LoopHaltImage.region mode origin l g)).map (StringStoreWrites.liftDword mode)++
  (Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions)
    (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))).map (StringStoreWrites.liftDword mode)

theorem shape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    Listing8LoopControl.program mode origin l t g node rule state++tail mode origin l g node rule=
      Listing8LoopTerminal.program mode origin l t g node rule state := by
  simp only [tail,Listing8LoopTerminal.program,Listing8LoopReset.program,Listing8LoopTable.program,
    Listing8GlobalLoopMainRegions.lift_dword,List.append_assoc]

/-- Reentry passes and the final halting main pass retain the SAME accepted
invariant. The phase graph and entry are bound to the actual complete prefix. -/
theorem main_prefix (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {l : Layout} {old : OldInput} {state : StringExecution.State mode}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    {lastL : Layout} {lastOld : OldInput} {lastState : StringExecution.State mode} {code : List (StringStack.Form mode)}
    (all : Listing8JointIteration.Run mode origin t g node rule l old state lastGraph lastNode lastRule lastL lastOld lastState code)
    (ctx : Context mode origin lastL t lastGraph lastNode lastRule)
    (image : Listing8LoopHaltImage.Current mode origin lastL t lastGraph lastNode lastRule lastOld lastState)
    (before after : List (StringStack.Form mode))
    (cut : code++Listing8LoopControl.program mode origin lastL t lastGraph lastNode lastRule lastState=before++after) :
    Listing8JointIteration.PrefixWitness mode origin t state before (StringWrites.run mode before state) := by
  rcases Listing8BoundarySummary.cut_append code _ before after cut with
    ⟨rest,split⟩ | ⟨pre,rest,split,location⟩
  · exact Listing8JointIteration.at_prefix mode origin t all before rest split
  · have actual := StringWrites.trace_run_eq mode (Listing8JointIteration.trace mode origin t all)
    refine ⟨lastGraph,lastNode,lastRule,lastL,lastOld,lastState,code,pre,rest,ctx,image,split,location,actual.symm,?_,?_⟩
    · rw [location,StringWrites.run_append,actual]
    · rw [location,StringWrites.run_append,actual]
      exact Listing8JointCopyOwnerLifetimes.complete mode origin lastL t lastGraph lastNode lastRule ctx lastOld lastState image.control pre rest split

/-- Finite source-graph execution constructs one fetched body trace. EVERY
prefix either carries the joint maintained-main witness or the final exact
terminal packet/catalog certificate. No future catalog or native run premise. -/
theorem execute (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (l : Layout) (old : OldInput) (state : StringExecution.State mode)
    (ctx : Context mode origin l t g node rule) (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : a.epilogue=Listing8JointAccumulatorCatalog.graphEnd mode origin lastGraph)
    (saveAfter : Listing8JointAccumulatorCatalog.graphEnd mode origin lastGraph≤a.save)
    (pointerAfter : Listing8JointAccumulatorCatalog.graphEnd mode origin lastGraph≤a.pointer) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode state code finalState ∧
      finalState.principal.pc.toNat=Listing8GraphLayout.endPC mode origin lastGraph.transitions lastGraph.nodes ∧
      code.length=count*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      ∀ before after,code=before++after →
        Listing8JointIteration.PrefixWitness mode origin t state before (StringWrites.run mode before state) ∨
        ∃ (lastL : Layout) (lead part rest : List (StringStack.Form mode)),
          tail mode origin lastL lastGraph lastNode lastRule=part++rest ∧ before=lead++part ∧
          Listing8JointAccumulatorCatalog.TerminalProperty mode origin lastL lastGraph lastNode lastRule
            (StringWrites.run mode before state).principal.memory := by
  obtain ⟨lastL,lastOld,lastState,prefixCode,lastCtx,lastImage,all,prefixTrace,prefixLength⟩ :=
    Listing8JointIteration.execute mode origin t logical l old state ctx image
  let main := Listing8LoopControl.program mode origin lastL t lastGraph lastNode lastRule lastState
  let ending := tail mode origin lastL lastGraph lastNode lastRule
  have tailTrace := Listing8LoopTerminal.trace mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  have terminal := Listing8JointAccumulatorCatalog.terminal_tail mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted a valid located saveAfter pointerAfter
  have mainTrace := Listing8LoopControl.trace mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage.control
  have mainRun := StringWrites.trace_run_eq mode mainTrace
  have initialRun := StringWrites.trace_run_eq mode prefixTrace
  have endpoint := Listing8LoopTerminal.endpoint mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  have length := Listing8LoopTerminal.instruction_count mode origin lastL t lastGraph lastNode lastRule lastState
  have terminalShape := shape mode origin lastL t lastGraph lastNode lastRule lastState
  change main++ending=_ at terminalShape
  rw [←terminalShape] at tailTrace length
  refine ⟨_,(prefixCode++main)++ending,?_,endpoint,?_,?_⟩
  · rw [List.append_assoc]
    exact StringStack.trace_append mode prefixTrace tailTrace
  · rw [List.length_append,List.length_append]
    rw [List.length_append] at length
    omega
  · intro before after cut
    rcases Listing8BoundarySummary.cut_append (prefixCode++main) ending before after cut with
      ⟨rest,split⟩ | ⟨part,rest,split,location⟩
    · exact Or.inl (main_prefix mode origin t all lastCtx lastImage before rest split)
    · refine Or.inr ⟨lastL,prefixCode++main,part,rest,split,location,?_⟩
      have completeCut : Listing8JointAccumulatorCatalog.tailForms mode origin lastL lastGraph lastNode lastRule a=
          part++(rest++Listing8AccumulatorExit.program mode a) := by
        change ending++Listing8AccumulatorExit.program mode a=_
        rw [split,List.append_assoc]
      have kept := StringTemplateStates.at_prefix mode _ part (rest++Listing8AccumulatorExit.program mode a)
        (Listing8LoopControl.finish mode origin lastL t lastGraph lastNode lastRule lastState) (completeCut ▸ terminal)
      rw [location,StringWrites.run_append,StringWrites.run_append,initialRun,mainRun]
      exact kept

/-- The phase-local witness remains tied to the complete maintained body. -/
@[expose] def BodyPrefix (mode : Mode) (origin : Nat) (t : Targets) (initial : StringExecution.State mode)
    (lastGraph : Graph) (lastNode : Fin lastGraph.nodes) (lastRule : Fin lastGraph.transitions)
    (before : List (StringStack.Form mode)) (reached : StringExecution.State mode) :=
  Listing8JointIteration.PrefixWitness mode origin t initial before reached ∨
  ∃ (lastL : Layout) (lead part rest : List (StringStack.Form mode)),
    tail mode origin lastL lastGraph lastNode lastRule=part++rest ∧ before=lead++part ∧
    Listing8JointAccumulatorCatalog.TerminalProperty mode origin lastL lastGraph lastNode lastRule reached.principal.memory

@[expose] def OriginalPrefix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (lastGraph : Graph) (lastNode : Fin lastGraph.nodes) (lastRule : Fin lastGraph.transitions)
    (body before : List (StringStack.Form mode)) (reached : StringExecution.State mode) :=
  (∃ rest,Listing4EntryLayout.forms mode origin=before++rest ∧
    Listing8BoundarySummary.BootstrapProperty mode origin l g reached.principal.memory) ∨
  ∃ part rest,body=part++rest ∧ before=Listing4EntryLayout.forms mode origin++part ∧
    BodyPrefix mode origin t (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)
      lastGraph lastNode lastRule part reached

/-- Original emission and bootstrap construct the first image. The full
joint invariant is transported across EVERY subsequent logical pass. -/
theorem original (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : a.epilogue=Listing8JointAccumulatorCatalog.graphEnd mode origin lastGraph)
    (saveAfter : Listing8JointAccumulatorCatalog.graphEnd mode origin lastGraph≤a.save)
    (pointerAfter : Listing8JointAccumulatorCatalog.graphEnd mode origin lastGraph≤a.pointer)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (body : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
        (Listing4EntryLayout.forms mode origin++body) finalState ∧
      finalState.principal.pc.toNat=Listing8GraphLayout.endPC mode origin lastGraph.transitions lastGraph.nodes ∧
      body.length=count*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      ∀ before after,Listing4EntryLayout.forms mode origin++body=before++after →
        OriginalPrefix mode origin l t g node rule memory seed lastGraph lastNode lastRule body before
          (StringWrites.run mode before (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)) := by
  have image := Listing8OriginalResetBinding.current mode origin l t g node rule ctx memory seed
  obtain ⟨finalState,body,bodyTrace,endpoint,length,prefixes⟩ :=
    execute mode origin t logical halted l Listing8OriginalControlImage.old _ ctx image a valid located saveAfter pointerAfter
  have boot : StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (Listing4EntryLayout.forms mode origin) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) :=
    Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  have bootRun := StringWrites.trace_run_eq mode boot
  refine ⟨finalState,body,StringStack.trace_append mode boot bodyTrace,endpoint,length,?_⟩
  intro before after cut
  rcases Listing8BoundarySummary.cut_append (Listing4EntryLayout.forms mode origin) body before after cut with
    ⟨rest,split⟩ | ⟨part,rest,split,location⟩
  · exact Or.inl ⟨rest,split,StringTemplateStates.at_prefix mode _ before rest _
      (split ▸ Listing8OriginalControlImage.bootstrap mode origin l t g node rule ctx memory seed)⟩
  · refine Or.inr ⟨part,rest,split,location,?_⟩
    rw [location,StringWrites.run_append,bootRun]
    exact prefixes part rest split

/-- The existing source-TM logical simulation lifts to the joint SAME-prefix
native body certificate. Only numeric/static placement resources are inputs;
all bootstrap,maintained and terminal images/traces are produced. -/
theorem complete_input {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (bounds : Listing9PackedLayout.Bounds mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length)))
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : a.epilogue=Listing8GraphLayout.endPC mode (Listing9PackedLayout.origin mode start)
      (states*(alphabet+1)) (Listing8TMRun.width (count+input.length)))
    (saveAfter : a.epilogue≤a.save) (pointerAfter : a.epilogue≤a.pointer)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (iterations : Nat) (lastNode : Fin (Listing8TMRun.width (count+input.length)))
      (finalState : StringExecution.State mode) (body : List (StringStack.Form mode)),
      Listing8TMWindow.position (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) lastNode=finish.head ∧
      StringStack.Trace mode
        (Listing8GraphBackedge.initial mode (Listing9PackedLayout.origin mode start)
          (Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length))
          (Listing9TMStaticExecution.bodyTargets mode start)
          (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
          (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) memory seed)
        (Listing4EntryLayout.forms mode (Listing9PackedLayout.origin mode start)++body) finalState ∧
      body.length=iterations*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+
        11*(states*(alphabet+1))+9*Listing8TMRun.width (count+input.length) ∧
      ∀ before after,Listing4EntryLayout.forms mode (Listing9PackedLayout.origin mode start)++body=before++after →
        OriginalPrefix mode (Listing9PackedLayout.origin mode start)
          (Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length))
          (Listing9TMStaticExecution.bodyTargets mode start)
          (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
          (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) memory seed
          (Listing8TMWindow.graph machine (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length))
            (Listing8TMRun.width (count+input.length)) (Listing8TMRun.positive (count+input.length)) finish)
          lastNode (Listing8TMRules.index finish.state (Listing8TMRules.endSlot alphabet)) body before
          (StringWrites.run mode before
            (Listing8GraphBackedge.initial mode (Listing9PackedLayout.origin mode start)
              (Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length))
              (Listing9TMStaticExecution.bodyTargets mode start)
              (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
              (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) memory seed)) := by
  obtain ⟨iterations,lastNode,bounded,head,logical,declaredHalt,unchanged⟩ :=
    Listing8TMObservedRun.finite_halt machine capacity (TM.initialConfiguration machine input) finish count input.length actual halted
  have ctx := Listing9PackedCapacity.context mode start
    (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
    (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) bounds
  obtain ⟨finalState,body,trace,endpoint,length,prefixes⟩ :=
    original mode (Listing9PackedLayout.origin mode start) _ _ logical declaredHalt ctx a valid located
      (by change Listing8GraphLayout.endPC mode (Listing9PackedLayout.origin mode start) (states*(alphabet+1)) (Listing8TMRun.width (count+input.length))≤a.save;rw [←located];exact saveAfter)
      (by change Listing8GraphLayout.endPC mode (Listing9PackedLayout.origin mode start) (states*(alphabet+1)) (Listing8TMRun.width (count+input.length))≤a.pointer;rw [←located];exact pointerAfter) memory seed
  exact ⟨iterations,lastNode,finalState,body,head,trace,length,prefixes⟩

end SmcTuring.Appendix.Listing8JointInterpreter

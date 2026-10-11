module
public import SmcTuring.Appendix.Listing8OriginalNativeHead
public import SmcTuring.Appendix.Listing9TMFixedOutput

public section
namespace SmcTuring.Appendix.Listing9NativeHeadObservation
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing9PackedLayout
abbrev Targets:=Listing8PointerCopies.Targets

/-- The one-time accumulator store and original packed image positively
derive a reached native head boundary; no boundary state/image is an input. -/
theorem execute (mode : Mode) (start : Nat) (lower : Int) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode (origin mode start) l t g node rule) (bounds : Bounds mode start g.transitions g.nodes)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (cursor : Nat) (boundary : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing9ExecutionImage.initial mode start l t g node rule memory seed) code boundary ∧
      Listing8NativeHeadBoundary.observe mode (origin mode start) lower lastGraph.transitions cursor boundary.principal.memory=
        lower+((Listing8GraphStep.nextNode lastGraph lastNode lastRule).val : Int) := by
  have valid:=admissible mode start g.transitions g.nodes bounds
  have coordinates:=positions mode start g.transitions g.nodes
  have ordered:=bounds_order mode start g.transitions g.nodes
  have first:=Listing8AccumulatorEntry.trace mode (origin mode start) l t g node rule (layout mode start g.transitions g.nodes) valid
    (Listing9Image.memory mode start g.transitions g.nodes memory) seed
    (Listing9ExecutionImage.prologue_current mode start l t g node rule ctx memory seed)
  rw [Listing8AccumulatorEntry.saved_eq mode (origin mode start) l t g node rule ctx (layout mode start g.transitions g.nodes) valid
    coordinates.1 (by change epilogue mode start g.transitions g.nodes≤_
                      exact Nat.le_trans ordered.2.1 ordered.2.2.1)] at first
  obtain ⟨cursor,boundary,code,actual,head⟩:=Listing8OriginalNativeHead.original_graph mode (origin mode start) lower l t
    logical halted ctx (ByteMemory.putWord mode (Listing9Image.memory mode start g.transitions g.nodes memory)
      (layout mode start g.transitions g.nodes).save seed.principal.accumulator) seed
  exact ⟨cursor,boundary,_,StringStack.trace_append mode first actual,head⟩

/-- For an actual completed source-TM input run, the emitted Listing 9
execution reaches a boundary whose physically stored cursor decodes to the
exact terminal source head. The final cleanup cursor is not observed here. -/
theorem complete_input {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      Listing8TMRun.width (count+input.length)*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (reach : mode=.x64 → 1474+(states*(alphabet+1))*84+Listing8TMRun.width (count+input.length)*64≤2^31)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (cursor : Nat) (boundary : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode
        (Listing9ExecutionImage.initial mode start
          (Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length))
          (Listing9TMStaticExecution.bodyTargets mode start)
          (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
          (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) memory seed)
        code boundary ∧
      Listing8NativeHeadBoundary.observe mode (origin mode start)
        (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length))
        (states*(alphabet+1)) cursor boundary.principal.memory=finish.head := by
  obtain ⟨iterations,lastNode,bounded,lastHead,logical,declaredHalt,unchanged⟩:=
    Listing8TMObservedRun.finite_halt machine capacity (TM.initialConfiguration machine input) finish count input.length actual halted
  have bounds:=Listing9PackedCapacity.bounds mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length)) capacityBytes reach
  have ctx:=Listing9PackedCapacity.context mode start
    (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
    (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) bounds
  obtain ⟨cursor,boundary,code,reached,head⟩:=execute mode start
    (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) _ _ logical declaredHalt ctx bounds memory seed
  have different:=Listing8TMRules.terminal_symbol machine capacity finish.state
    (Listing8TMWindow.tape (width:=Listing8TMRun.width (count+input.length))
      (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) finish lastNode)
  have stayed:=Listing8TMGraph.mismatch_node machine (⟨0,Listing8TMRun.positive (count+input.length)⟩ : Fin (Listing8TMRun.width (count+input.length)))
    Listing8TMWindow.back Listing8TMWindow.forward
    (Listing8TMWindow.tape (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) finish)
    lastNode (Listing8TMRules.index finish.state (Listing8TMRules.endSlot alphabet)) different
  rw [stayed] at head
  exact ⟨cursor,boundary,code,reached,head.trans lastHead⟩

end SmcTuring.Appendix.Listing9NativeHeadObservation

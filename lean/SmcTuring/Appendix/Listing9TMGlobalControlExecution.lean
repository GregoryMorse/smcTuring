module
public import SmcTuring.Appendix.Listing9GlobalControlExecution
public import SmcTuring.Appendix.Listing9NativeHeadObservation

public section
namespace SmcTuring.Appendix.Listing9TMGlobalControlExecution
open Native Listing9PackedLayout
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

/-- Source execution and numeric bounds construct one complete native trace.
The global thirteen/eighteen control descriptors and six/twelve late templates
jointly decode at every reached prefix, including both immediate and later halts. -/
theorem complete_input {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (halted : TM.step machine finish=none)
    (mode : Mode) (start : Nat)
    (capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      Listing8TMRun.width (count+input.length)*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (reach : mode=.x64 → 1474+(states*(alphabet+1))*84+Listing8TMRun.width (count+input.length)*64≤2^31)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode
        (Listing9ExecutionImage.initial mode start
          (Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length))
          (Listing9TMStaticExecution.bodyTargets mode start)
          (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
          (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) memory seed)
        code finalState ∧
      StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode (origin mode start) reached.principal.memory ∧
        Listing9TailTemplates.Decodes mode start
        (states*(alphabet+1)) (Listing8TMRun.width (count+input.length)) reached.principal.memory) code
        (Listing9ExecutionImage.initial mode start
          (Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length))
          (Listing9TMStaticExecution.bodyTargets mode start)
          (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
          (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) memory seed) ∧
      finalState.principal.pc.toNat=Listing9PackedLayout.endPC mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length)) := by
  obtain ⟨iterations,lastNode,bounded,lastHead,logical,declaredHalt,unchanged⟩:=
    Listing8TMObservedRun.finite_halt machine capacity (TM.initialConfiguration machine input) finish count input.length actual halted
  have bounds:=Listing9PackedCapacity.bounds mode start (states*(alphabet+1)) (Listing8TMRun.width (count+input.length)) capacityBytes reach
  have ctx:=Listing9PackedCapacity.context mode start
    (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
    (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state) bounds
  obtain ⟨finalState,code,trace,templates,endpoint,length⟩:=
    Listing9GlobalControlExecution.execute mode start _ _ logical declaredHalt ctx bounds memory seed
  exact ⟨finalState,code,trace,templates,endpoint⟩

end SmcTuring.Appendix.Listing9TMGlobalControlExecution

module
public import SmcTuring.Appendix.Listing8GlobalIterationTemplates
public import SmcTuring.Appendix.Listing8GlobalMaintainedTerminalTemplates

public section
namespace SmcTuring.Appendix.Listing8GlobalMaintainedInterpreterTemplates
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

/-- A maintained finite source-graph continuation constructs all native
iterations, final main/CALL, transition/reset and node declarations, with the
global catalog at every prefix. Every later entry/image/trace is concluded. -/
theorem execute (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (l : Layout) (old : OldInput) (state : StringExecution.State mode)
    (ctx : Context mode origin l t g node rule)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode state code finalState ∧
      StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory) code state ∧
      Listing8GlobalControlTemplates.Property mode origin finalState.principal.memory ∧
      finalState.principal.pc.toNat=Listing8GraphLayout.endPC mode origin lastGraph.transitions lastGraph.nodes ∧
      code.length=count*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes := by
  obtain ⟨lastL,lastOld,lastState,prefixCode,lastCtx,lastImage,prefixTrace,prefixTemplates,prefixLength⟩:=
    Listing8GlobalIterationTemplates.execute mode origin t logical l old state ctx image
  have terminal:=Listing8GlobalMaintainedTerminalTemplates.execute mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  refine ⟨Listing8LoopTerminal.finish mode origin lastL t lastGraph lastNode lastRule lastState,
    prefixCode++Listing8LoopTerminal.program mode origin lastL t lastGraph lastNode lastRule lastState,
    StringStack.trace_append mode prefixTrace terminal.1,?_,
    Listing8GlobalMaintainedTerminalTemplates.property mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted,
    Listing8LoopTerminal.endpoint mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted,?_⟩
  · rw [StringTemplateStates.append,StringWrites.trace_run_eq mode prefixTrace]
    exact ⟨prefixTemplates,terminal.2⟩
  · rw [List.length_append,prefixLength,Listing8LoopTerminal.instruction_count]
    omega

end SmcTuring.Appendix.Listing8GlobalMaintainedInterpreterTemplates

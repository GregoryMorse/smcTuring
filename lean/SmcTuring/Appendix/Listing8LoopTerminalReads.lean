module
public import SmcTuring.Appendix.Listing8LoopReads
public import SmcTuring.Appendix.Listing8LoopTerminalBodyWrites
public import SmcTuring.Appendix.Listing8TerminalReadClasses

public section
namespace SmcTuring.Appendix.Listing8LoopTerminalReads
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

theorem tail_local (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    ∀ form∈Listing8LoopTerminalWrites.program mode origin l t g node rule state,StringReadWindows.Local mode form := by
  simp only [Listing8LoopTerminalWrites.program,List.mem_append]
  intro form member
  rcases member with ((jump | table) | reset) | nodes
  · exact Listing8TailReadClasses.jump_return mode _ _ form jump
  · exact Listing8TerminalReadClasses.transitions mode _ _ form table
  · exact Listing8TerminalReadClasses.reset mode _ form reset
  · exact Listing8TerminalReadClasses.nodes mode _ _ form nodes

/-- Every read of the actual final body, failed CALL/return, original table,
reset/DOHALT and updated input declarations follows the maintained entry. -/
theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8LoopTerminal.program mode origin l t g node rule state) state := by
  rw [Listing8LoopTerminalBodyWrites.program_split]
  exact StringReadRuns.append_trace mode _ _ _ state
    (Listing8LoopControl.failureEnd mode origin l t g node rule state)
    (Listing8LoopGraphFailure.trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
      (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) image.control.body)
    (Listing8LoopReads.failure mode origin l t g node rule ctx old state image.control.body)
    (StringReadRuns.local_of_owned mode origin _ _ _ (tail_local mode origin l t g node rule state)
      (Listing8LoopTerminalWrites.owned mode origin l t g node rule ctx old state image halted))

end SmcTuring.Appendix.Listing8LoopTerminalReads

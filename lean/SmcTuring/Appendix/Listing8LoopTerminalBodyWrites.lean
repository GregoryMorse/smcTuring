module
public import SmcTuring.Appendix.Listing8LoopControlWrites
public import SmcTuring.Appendix.Listing8LoopTerminalWrites

public section
namespace SmcTuring.Appendix.Listing8LoopTerminalBodyWrites
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets := Listing8PointerCopies.Targets
abbrev OldInput := Listing8MainInput.OldInput

theorem program_split (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    Listing8LoopTerminal.program mode origin l t g node rule state=
      (Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous++
      Listing8LoopTerminalWrites.program mode origin l t g node rule state := by
  simp only [Listing8LoopTerminal.program,Listing8LoopReset.program,Listing8LoopTable.program,
    Listing8LoopControl.program,Listing8LoopTerminalWrites.program,Listing8GraphHaltTerminalWrites.tableForms,
    Listing8GraphHaltTerminalWrites.resetForms,Listing8GraphHaltTerminalWrites.nodeForms,
    Listing8GraphHaltTerminalWrites.resetRegion,Listing8LoopHaltImage.region,
    List.map_map,Function.comp_def,List.append_assoc]
  rfl

/-- Complete repeated terminal iteration, including the whole body before
CALL, every transition/reset/DOHALT and updated input/node declaration. -/
theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8LoopTerminal.program mode origin l t g node rule state) state := by
  rw [program_split]
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ state (Listing8LoopControl.failureEnd mode origin l t g node rule state)
  · exact Listing8LoopGraphFailure.trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
      (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) image.control.body
  · exact Listing8LoopFailureWrites.owned mode origin l t g node rule ctx old state image.control.body
  · exact Listing8LoopTerminalWrites.owned mode origin l t g node rule ctx old state image halted

end SmcTuring.Appendix.Listing8LoopTerminalBodyWrites

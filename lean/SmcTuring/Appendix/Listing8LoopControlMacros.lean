module
public import SmcTuring.Appendix.Listing8LoopControlFrames
public import SmcTuring.Appendix.Listing8LoopPrefixBodyFrames

public section
namespace SmcTuring.Appendix.Listing8LoopControlMacros
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev params:=Listing8MainInputMacroWindows.params

theorem header (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) (second : Bool) :
    ByteMemory.bytesAt (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory (params mode l second).start (StringCodec.fieldOffset mode)=StringInit.leading mode (params mode l second).start := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have bounds:=Listing8GraphMainFrames.header_bounds mode l ctx.body.state.head.input.fields.cursorLabel second
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  dsimp only [Listing8LoopControl.failureEnd,params,Listing8MainInputMacroWindows.params]
  rw [Listing8LoopPrefixBodyFrames.failure mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state image.body.state.head.graph.entry image.body.state.head.graph.forward input _ _
    (Nat.le_trans bounds.1 (by omega)) bounds.2.1 bounds.2.2]
  exact Listing8MainInputMacroWindows.header mode l t (values mode origin g node rule) old b.state.head.input state image.body.state.head.graph.entry image.body.state.head.graph.forward input.state.head.input second

theorem tail (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) (second : Bool) :
    ByteMemory.bytesAt (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory ((params mode l second).start+StringCodec.initialSize mode) (StringMacroSource.tailBytes mode (params mode l second)).length=StringMacroSource.tailBytes mode (params mode l second) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have bounds:=Listing8GraphMainFrames.tail_bounds mode l ctx.body.state.head.input.fields.cursorLabel second
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  dsimp only [Listing8LoopControl.failureEnd,params,Listing8MainInputMacroWindows.params]
  rw [Listing8LoopPrefixBodyFrames.failure mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state image.body.state.head.graph.entry image.body.state.head.graph.forward input _ _
    (Nat.le_trans bounds.1 (by omega)) bounds.2.1 bounds.2.2]
  exact Listing8MainInputMacroWindows.tail mode l t (values mode origin g node rule) old b.state.head.input state image.body.state.head.graph.entry image.body.state.head.graph.forward input.state.head.input second

theorem node_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) (target : Fin g.transitions) :
    Listing8MainCopyImage.MacroCurrent mode (nodeParams mode (nextLayout mode origin l g node rule target)) (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory := by
  refine ⟨header mode origin l t g node rule ctx old state image false,tail mode origin l t g node rule ctx old state image false,?_⟩
  have actual:=Listing8LoopControlFrames.logical_head mode origin l t g node rule ctx old state image
  rw [ctx.body.state.head.input.fields.cursorLabel] at actual
  exact actual

theorem rule_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) (target : Fin g.transitions) (selected : Listing8GraphStep.nextRule g node rule=some target) :
    Listing8MainCopyImage.MacroCurrent mode (transitionParams mode (nextLayout mode origin l g node rule target)) (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory := by
  refine ⟨header mode origin l t g node rule ctx old state image true,tail mode origin l t g node rule ctx old state image true,?_⟩
  have actual:=Listing8LoopControlFrames.logical_transition mode origin l t g node rule ctx old state image
  rw [selected] at actual
  exact actual

end SmcTuring.Appendix.Listing8LoopControlMacros

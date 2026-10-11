module
public import SmcTuring.Appendix.Listing8LoopControl

public section
namespace SmcTuring.Appendix.Listing8LoopControlFrames
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem logical_head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    MixedMemory.getWord mode (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory l.input.cursor=Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) := by
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8LoopGraphFailure.logical_head mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
    (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) image.body

theorem logical_transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    MixedMemory.getWord mode (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode (statePC mode origin g (Listing8GraphStep.nextRule g node rule)) := by
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8LoopGraphFailure.logical_transition mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
    (Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx) image.body

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule)) (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory := by
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8LoopGraphFailure.source_graph mode origin l t g node rule ctx old state image.body

theorem direction_fragments (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l) (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8LoopFailureFrames.direction_fragments mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state image.body.state.head.graph.entry image.body.state.head.graph.forward input

theorem state_fragments (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    Listing8LoopStateImage.Current mode (Listing8StateGeometry.region mode l) (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8LoopFailureFrames.state_fragments mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state image.body.state.head.graph.entry image.body.state.head.graph.forward input

theorem failure_fragments (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    Listing8FailureReuseImage.Current mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8LoopFailure.current_after mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state image.body.state.head.graph.entry image.body.state.head.graph.forward input

theorem entry_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin := by
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8LoopControlImage.entry_packet mode origin l t g node rule ctx old state image

theorem prefix_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory (Listing8JumpLayout.jumpPC mode origin) ((Listing8JumpLayout.prefixBytes mode origin).length)=Listing8JumpLayout.prefixBytes mode origin := by
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8LoopControlImage.prefix_packet mode origin l t g node rule ctx old state image

theorem fail_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory (Listing8JumpLayout.failPC mode origin) (Listing4TargetLayout.size mode)=Listing8FailLayout.bytes mode origin := by
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8LoopControlImage.fail_packet mode origin l t g node rule ctx old state image

theorem call_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory (Listing8JumpLayout.callPC mode origin) 5=Native.encode mode (Listing8JumpLayout.call mode origin (Listing8LoopControl.failed mode origin l t g node rule state)) := by
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx old state image]
  exact Listing8LoopControlImage.call_packet mode origin l t g node rule ctx old state image

end SmcTuring.Appendix.Listing8LoopControlFrames

module
public import SmcTuring.Appendix.Listing8LoopTable
public import SmcTuring.Appendix.Listing8LoopReentry
public import SmcTuring.Appendix.Listing8LoopLateFrames
public import SmcTuring.Appendix.Listing8LoopBackedgeControlImage
public import SmcTuring.Appendix.Listing8GraphNextResetImage

public section
namespace SmcTuring.Appendix.Listing8LoopHaltImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
@[expose] def region (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) :=
  Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)

/-- The reset/DOHALT bytes and all body/control observations refer to the
same present main-entry memory. Reached reset images are derived. -/
structure Current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (machine : StringExecution.State mode) : Prop where
  control : Listing8LoopControl.Current mode origin l t g node rule old machine
  reset : Listing8ResetPackets.Initial mode (region mode origin l g) machine.principal.memory

theorem region_next (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (target : Fin g.transitions) :
    region mode origin (nextLayout mode origin l g node rule target) (Listing8GraphStep.updated g node rule)=region mode origin l g := by
  simp only [region,Listing8TableResetImage.region,Listing8TransitionTable.endPC,table_length]
  rfl

theorem after_control (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    Listing8ResetPackets.Initial mode (region mode origin l g) (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory := by
  have bounds:=Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.control.body
  have after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5≤(region mode origin l g).start := by
    have location:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
    change Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.callPC mode origin at location
    rw [location]
    exact bounds.reset.callBefore
  have tapeOutside : l.sourceNode+10≤(region mode origin l g).start ∨ (region mode origin l g).start+(Listing8ResetLayout.bytes mode (region mode origin l g)).length≤l.sourceNode+6 := by
    right
    rw [Listing8ResetLayout.bytes_length,←(Listing8ResetLayout.positions mode (region mode origin l g)).2.2.2]
    have before:=bounds.nodeAfter
    change Listing8ResetLayout.endPC mode (region mode origin l g)≤l.sourceNode at before
    omega
  rw [Listing8ResetPackets.Initial,Listing8LoopControl.memory mode origin l t g node rule ctx old state image.control]
  dsimp only [Listing8LoopControl.failureEnd]
  rw [Listing8LoopLateFrames.failure_window mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state image.control.body.state.head.graph.entry image.control.body.state.head.graph.forward input _ _ after tapeOutside]
  exact image.reset

theorem after_control_source (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) :
    MixedMemory.getWord mode (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory (region mode origin l g).inputSource=Arithmetic.encodeNat mode (nodePC mode origin g g.halt) := by
  let fragment:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have current:=Listing8LoopControlFrames.failure_fragments mode origin l t g node rule ctx old state image.control
  have cap:=Listing8FailureBounds.owner_fits mode fragment (Listing8FailureGeometry.local_bounds mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.resources ctx.body)
  have ending:=Listing8FailureLayout.source_end mode fragment
  have fits : Listing8FailureLayout.source mode fragment<2^(8*mode.wordBytes) := by
    change Listing8FailureLayout.comparisonPC mode fragment<_ at cap
    have positive : 0<mode.wordBytes := by cases mode <;> decide
    omega
  have value:=StringInit.initialized_pointer mode (Listing8FailureLayout.ownerPC fragment) (nodePC mode origin g g.halt) (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory cap current.ownerImage
  change Execution.load mode _ (Arithmetic.encodeNat mode (Listing8FailureLayout.source mode fragment))=_ at value
  rw [MixedMemory.load_nat mode _ _ fits] at value
  exact value

theorem after_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) (halted : Listing8GraphRun.Halted g node rule) :
    Listing8ResetPackets.Initial mode (region mode origin l g) (Listing8LoopTable.finish mode origin l t g node rule state).principal.memory := by
  rw [(Listing8LoopTable.result mode origin l t g node rule ctx old state image.control halted).2.1]
  exact after_control mode origin l t g node rule ctx old state image

theorem after_table_source (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) (halted : Listing8GraphRun.Halted g node rule) :
    MixedMemory.getWord mode (Listing8LoopTable.finish mode origin l t g node rule state).principal.memory (region mode origin l g).inputSource=Arithmetic.encodeNat mode (nodePC mode origin g g.halt) := by
  rw [(Listing8LoopTable.result mode origin l t g node rule ctx old state image.control halted).2.1]
  exact after_control_source mode origin l t g node rule ctx old state image

theorem reentry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (image : Current mode origin l t g node rule old state) (target : Fin g.transitions) (selected : Listing8GraphStep.nextRule g node rule=some target) :
    Current mode origin (nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
      (Listing8LoopControlReentryFields.old mode origin g node rule) (Listing8LoopControl.finish mode origin l t g node rule state) := by
  refine ⟨Listing8LoopReentry.current mode origin l t g node rule ctx old state image.control target selected,?_⟩
  rw [region_next mode origin l t g node rule target]
  exact after_control mode origin l t g node rule ctx old state image

theorem after_backedge (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Current mode origin (nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
      (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) := by
  refine ⟨Listing8LoopBackedgeControlImage.current mode origin l t g node rule target ctx selected memory seed,?_⟩
  rw [region_next mode origin l t g node rule target]
  exact Listing8GraphNextResetImage.after_backedge mode origin l t g node rule ctx memory seed

end SmcTuring.Appendix.Listing8LoopHaltImage

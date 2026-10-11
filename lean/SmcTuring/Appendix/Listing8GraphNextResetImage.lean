module
public import SmcTuring.Appendix.Listing8GraphNextTable

public section
namespace SmcTuring.Appendix.Listing8GraphNextResetImage
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8ResetLayout.Bounds mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)) :=
  (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset

theorem node_after (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8ResetLayout.endPC mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))≤
      (nextLayout mode origin l g node rule target).sourceNode := by
  rw [Listing8GraphReset.actual_region mode origin l t (nodePC mode origin g g.halt) (table mode origin g) ctx.boot ctx.body,
    table_length,Listing8GraphReset.endpoint]
  exact Listing8GraphLayout.node_lower mode origin g.transitions (Listing8GraphStep.nextNode g node rule).val

theorem after_backedge (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8ResetPackets.Initial mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory := by
  let reset:=Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)
  have selectedSpan:=Listing8TransitionTable.fields_bounds mode (Listing8FullTableImage.start mode origin) (table mode origin g) rule.val
    (values mode origin g node rule) (Listing8SourceGraph.selected mode origin g node rule)
  have located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) rule.val := by
    rw [ctx.ruleLocated];rfl
  have tableBefore : Listing8FullTableImage.start mode origin≤reset.start := by
    dsimp [reset,Listing8TableResetImage.region,Listing8TransitionTable.endPC];omega
  have after : Listing8JumpLayout.failPC mode origin≤reset.start := by
    dsimp [Listing8FullTableImage.start,Listing8FailLayout.endPC] at tableBefore;omega
  have sourceOutside : l.sourceTransition+transitionSpan mode≤reset.start := by
    rw [located];exact selectedSpan.2
  have nodeOutside : reset.start+(Listing8ResetLayout.bytes mode reset).length≤l.sourceNode := by
    rw [Listing8ResetLayout.bytes_length,←(Listing8ResetLayout.positions mode reset).2.2.2]
    exact (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).nodeAfter
  rw [Listing8ResetPackets.Initial,Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  change ByteMemory.bytesAt (Listing8GlobalJump.bodyEnd mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (Listing8GraphBackedge.backing mode origin l g memory) seed).principal.memory reset.start (Listing8ResetLayout.bytes mode reset).length=Listing8ResetLayout.bytes mode reset
  rw [Listing8ResetImage.body_window mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body _ seed _ _ after (Or.inr nodeOutside) (Or.inl sourceOutside),
    Listing8GraphBackedge.backing,Listing8FailImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
      rw [Listing8FailLayout.bytes_length];exact tableBefore)),
    Listing8FullTableImage.backing,Listing8TransitionTable.image,byte_frame _ _ _ _ _ (Or.inl (by
      rw [Listing8TransitionTable.endpoint];exact Nat.le_refl _))]
  exact ByteMemory.bytes_at_put _ _ _

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8ResetPackets.Initial mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))
      (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory := by
  let reset:=Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)
  have tableBefore : Listing8FullTableImage.start mode origin≤reset.start := by
    dsimp [reset,Listing8TableResetImage.region,Listing8TransitionTable.endPC];omega
  have position:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.callPC mode origin at position
  have after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5≤reset.start := by
    rw [position]
    dsimp [Listing8FullTableImage.start,Listing8FailLayout.endPC,Listing8JumpLayout.failPC] at tableBefore;omega
  have tapeOutside : (nextLayout mode origin l g node rule target).sourceNode+10≤reset.start ∨
      reset.start+(Listing8ResetLayout.bytes mode reset).length≤(nextLayout mode origin l g node rule target).sourceNode+6 := by
    right
    rw [Listing8ResetLayout.bytes_length,←(Listing8ResetLayout.positions mode reset).2.2.2]
    have later:=node_after mode origin l t g node rule target ctx
    change Listing8ResetLayout.endPC mode reset≤(nextLayout mode origin l g node rule target).sourceNode at later
    omega
  rw [Listing8ResetPackets.Initial,Listing8GraphNextLateBody.after_failure mode origin l t g node rule target ctx selected memory seed _ _ after tapeOutside]
  exact after_backedge mode origin l t g node rule ctx memory seed

theorem after_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    Listing8ResetPackets.Initial mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))
      (Listing8GraphNextTable.finish mode origin l t g node rule target memory seed).principal.memory := by
  rw [Listing8GraphNextTable.memory_effect mode origin l t g node rule target ctx selected memory seed halted]
  exact current mode origin l t g node rule target ctx selected memory seed

theorem source_value (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :
    MixedMemory.getWord mode (Listing8GraphNextTable.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)).inputSource=
        Arithmetic.encodeNat mode (nodePC mode origin g g.halt) := by
  rw [Listing8GraphNextTable.memory_effect mode origin l t g node rule target ctx selected memory seed halted]
  let fragment:=Listing8BootControl.region mode origin l (nodePC mode origin g g.halt)
  have known:=Listing8FailureReuseEffects.current_after mode fragment
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)
  have cap:=Listing8FailureBounds.owner_fits mode fragment (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body)
  have fits : Listing8FailureLayout.source mode fragment<2^(8*mode.wordBytes) := by
    have ending:=Listing8FailureLayout.source_end mode fragment
    change Listing8FailureLayout.comparisonPC mode fragment<_ at cap
    have positive : 0<mode.wordBytes := by cases mode <;> decide
    omega
  have value:=StringInit.initialized_pointer mode (Listing8FailureLayout.ownerPC fragment) (nodePC mode origin g g.halt) _ cap known.ownerImage
  change Execution.load mode _ (Arithmetic.encodeNat mode (Listing8FailureLayout.source mode fragment))=_ at value
  rw [MixedMemory.load_nat mode _ _ fits] at value
  exact value

end SmcTuring.Appendix.Listing8GraphNextResetImage

module
public import SmcTuring.Appendix.Listing8GraphNextLateBody

public section
namespace SmcTuring.Appendix.Listing8GraphNextFailImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem tail_bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8FailLayout.Bounds mode origin l (Listing8FullTableImage.start mode origin) := by
  have located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) rule.val := by
    rw [ctx.ruleLocated];rfl
  exact Listing8FullTableImage.fail_bounds mode origin l (table mode origin g) rule.val (values mode origin g node rule)
    (Listing8SourceGraph.selected mode origin g node rule) located
    (Listing8GraphTableBounds.table_bounds mode origin g node l ctx.nodeLocated ctx.native)

theorem after_backedge (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory
      (Listing8JumpLayout.failPC mode origin) (Listing4TargetLayout.size mode)=Listing8FailLayout.bytes mode origin := by
  rw [Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  exact Listing8FailImage.current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (Listing8FullTableImage.start mode origin) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
    (tail_bounds mode origin l t g node rule ctx)
    (Listing8FullTableImage.backing mode origin (table mode origin g) (Listing8TableResetImage.backing mode origin l
      (nodePC mode origin g g.halt) (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory))) seed

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8JumpLayout.failPC mode origin) (Listing4TargetLayout.size mode)=Listing8FailLayout.bytes mode origin := by
  have position:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.callPC mode origin at position
  have after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5≤Listing8JumpLayout.failPC mode origin := by
    rw [position];rfl
  have tapeOutside : (nextLayout mode origin l g node rule target).sourceNode+10≤Listing8JumpLayout.failPC mode origin ∨
      Listing8JumpLayout.failPC mode origin+Listing4TargetLayout.size mode≤(nextLayout mode origin l g node rule target).sourceNode+6 := by
    right
    have nextAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule)
    change Listing8FullTableImage.start mode origin≤nodePC mode origin g (Listing8GraphStep.nextNode g node rule)+6
    omega
  rw [Listing8GraphNextLateBody.after_failure mode origin l t g node rule target ctx selected memory seed _ _ after tapeOutside]
  exact after_backedge mode origin l t g node rule ctx memory seed

end SmcTuring.Appendix.Listing8GraphNextFailImage

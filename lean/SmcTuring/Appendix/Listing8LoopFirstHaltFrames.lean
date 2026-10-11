module
public import SmcTuring.Appendix.Listing8LoopInterpreterAnchor

public section
namespace SmcTuring.Appendix.Listing8LoopFirstHaltFrames
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

/-- The actual original reset preserves every window after CALL. Its only
writes are positively computed and lie in the earlier CALL/cursor fields. -/
theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : Listing8JumpLayout.callPC mode origin+5≤observed) :
    ByteMemory.bytesAt (Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8FullTableReset.entryState mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory) seed).principal.memory observed count := by
  have cursors:=Listing8GraphNextReset.cursors_before_call mode origin l t g node rule ctx
  rw [Listing8GraphRun.finish,Listing8FullTableReset.effect mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx) (Listing8GraphNodeImage.image mode origin g memory) seed,
    StackWindows.word_window _ _ _ _ _ _ (Or.inl (by have bound:=cursors.2;omega)),
    StackWindows.word_window _ _ _ _ _ _ (Or.inl (by have bound:=cursors.1;omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl (by omega))]

theorem rules (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8GraphRun.finish mode origin l t g node rule memory seed).principal.memory := by
  have after : Listing8JumpLayout.callPC mode origin+5≤Listing8FullTableImage.start mode origin := by
    dsimp [Listing8FullTableImage.start,Listing8FailLayout.endPC,Listing8JumpLayout.failPC];omega
  rw [Listing8TransitionTable.Initial,window mode origin l t g node rule ctx memory seed _ _ after,Listing8FullTableReset.entryState,
    (Listing8FullTable.result mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx).declarations (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory)) seed).2.1]
  exact Listing8FullTableImage.body_current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx).declarations (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory)) seed

end SmcTuring.Appendix.Listing8LoopFirstHaltFrames

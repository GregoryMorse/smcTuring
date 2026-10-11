module
public import SmcTuring.Appendix.Listing8LoopInterpreterTail

public section
namespace SmcTuring.Appendix.Listing8LoopOriginalTailFrames
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem initial_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤observed) :
    ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory) observed count=ByteMemory.bytesAt memory observed count := by
  have lower:=Nat.le_trans (Listing8LoopTailGeometry.input_before_end mode origin g) after
  have call:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx) lower
  let fragment:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have endBefore : Listing8FailureLayout.endPC mode fragment≤observed := by
    change Listing8FailureLayout.callPC mode fragment+5≤observed at call
    dsimp only [Listing8FailureLayout.callPC] at call
    omega
  have startBefore : fragment.start≤observed := by
    have coords:=Listing8FailureLayout.positions mode fragment
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have regionBefore : fragment.start+(Listing8FailureLayout.bytes mode fragment).length≤observed := by
    rw [Listing8FailureLayout.bytes_length,←(Listing8FailureLayout.positions mode fragment).2.2.2.1]
    exact endBefore
  have callBefore : Listing8FailureLayout.callPC mode fragment+
      (Listing8FailureGlobalImage.callBytes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).length≤observed := by
    have size : (Listing8FailureGlobalImage.callBytes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).length=5 := by cases mode <;> rfl
    rw [size];exact call
  rw [initialMemory,Listing8LateFrames.initial_image mode l t (values mode origin g node rule) _ _ ctx.resources ctx.body _ _ _ startBefore
    (Or.inl (Nat.le_trans (Listing8LoopTailGeometry.source_node_before_end mode origin l t g node rule ctx) after))
    (Or.inl (Nat.le_trans (Listing8LoopTailGeometry.source_rule_before_end mode origin l t g node rule ctx) after)),
    Listing8FailureGlobalImage.backing,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl regionBefore),
    Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl callBefore),
    Listing8GraphInputInitial.extra_window mode origin l t g node rule ctx memory observed count lower,
    Listing8GraphNodeImage.image,Listing8NodeTable.image,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by
      rw [Listing8NodeTable.endpoint,Listing8GraphNodeImage.endpoint];exact after))]

theorem body_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤observed) :
    ByteMemory.bytesAt (bodyEnd mode origin l t g node rule memory seed).principal.memory observed count=ByteMemory.bytesAt memory observed count := by
  have call:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
    (Nat.le_trans (Listing8LoopTailGeometry.input_before_end mode origin g) after)
  have outside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6 := by
    left
    have upper:=Listing8LoopTailGeometry.source_node_before_end mode origin l t g node rule ctx
    have large : 10≤Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
    omega
  rw [Listing8GraphBodyNodes.window mode origin l t g node rule ctx memory seed observed count call outside]
  exact initial_window mode origin l t g node rule ctx memory seed observed count after

theorem backedge_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤observed) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count=ByteMemory.bytesAt memory observed count := by
  rw [Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  exact body_window mode origin l t g node rule ctx memory seed observed count after

theorem first_halt_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) (observed count : Nat) (after : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤observed) :
    ByteMemory.bytesAt (Listing8LoopFirstHalt.finish mode origin l t g node rule memory seed).principal.memory observed count=ByteMemory.bytesAt memory observed count := by
  rw [(Listing8LoopFirstHalt.result mode origin l t g node rule ctx memory seed halted).2.1,
    Listing8LoopFirstHaltFrames.window mode origin l t g node rule ctx memory seed observed count (Nat.le_trans (Listing8LoopTailGeometry.call_before_end mode origin l t g node rule ctx) after),
    Listing8FullTableReset.entryState,
    (Listing8FullTable.result mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) (table mode origin g) rule.val (selected mode origin g node rule) ctx.ruleLocated ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (reset_bounds mode origin l t g node rule ctx).declarations (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory)) seed).2.1]
  exact body_window mode origin l t g node rule ctx memory seed observed count after

end SmcTuring.Appendix.Listing8LoopOriginalTailFrames

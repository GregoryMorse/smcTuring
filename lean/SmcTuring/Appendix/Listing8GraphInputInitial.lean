module
public import SmcTuring.Appendix.Listing8GraphInputContext

public section
namespace SmcTuring.Appendix.Listing8GraphInputInitial
open Native Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext

theorem call_before_input (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin))+5≤Listing8GraphLayout.input mode origin g.transitions := by
  have lower:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions)
    (Listing8GraphLayout.table_before_input mode origin g.transitions)
  change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l (nodePC mode origin g g.halt))+5≤_
  rw [Listing8JumpImage.call_position mode origin l t _ ctx.boot ctx.body,(Listing8JumpLayout.positions mode origin).1]
  rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset] at lower
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at lower ⊢ <;> omega

theorem extra_window (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (observed count : Nat) (after : Listing8GraphLayout.input mode origin g.transitions≤observed) :
    ByteMemory.bytesAt (extra mode origin l g memory) observed count=
      ByteMemory.bytesAt (Listing8GraphNodeImage.image mode origin g memory) observed count := by
  have tableBefore:=Listing8GraphLayout.table_before_input mode origin g.transitions
  have lower:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions) (Nat.le_trans tableBefore after)
  have bootBefore : origin+Listing4EntryLayout.size mode≤observed := by
    rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset] at lower
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,Listing4EntryLayout.size] at lower ⊢ <;> omega
  have prefixBefore : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length≤observed := by
    rw [Listing8JumpLayout.prefix_length]
    change Listing8JumpLayout.callPC mode origin≤observed
    have call:=Nat.le_trans (call_before_input mode origin l t g node rule ctx) after
    change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l (nodePC mode origin g g.halt))+5≤observed at call
    rw [Listing8JumpImage.call_position mode origin l t _ ctx.boot ctx.body] at call
    omega
  have tableEnd : Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)≤observed := by
    simp only [Listing8TransitionTable.endPC,table_length]
    exact Nat.le_trans tableBefore after
  have resetEnd : (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)).start+
      (Listing8ResetLayout.bytes mode (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g))).length≤observed := by
    rw [Listing8ResetLayout.bytes_length,←(Listing8ResetLayout.positions mode (Listing8TableResetImage.region mode origin l
      (nodePC mode origin g g.halt) (table mode origin g))).2.2.2,
      Listing8GraphReset.actual_region mode origin l t _ (table mode origin g) ctx.boot ctx.body,
      Listing8GraphReset.endpoint,table_length]
    exact after
  rw [extra,Listing8GlobalBoot.extra,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing4EntryLayout.bytes_length];exact bootBefore)),Listing8JumpImage.backing,
    Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl prefixBefore),Listing8FailImage.backing,
    Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by rw [Listing8FailLayout.bytes_length];exact lower)),
    Listing8FullTableImage.backing,Listing8TransitionTable.image,
    Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by rw [Listing8TransitionTable.endpoint];exact tableEnd)),
    Listing8TableResetImage.backing,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl resetEnd)]

theorem source_current (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) :
    ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory) (nodePC mode origin g node) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g node) (Listing8GraphNodeImage.value mode origin g node) := by
  have current : ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory) l.sourceNode
      (Listing8CopyImage.sourceNodeBytes mode l (values mode origin g node rule)).length=
      Listing8CopyImage.sourceNodeBytes mode l (values mode origin g node rule) :=
    Listing8CopyImage.initial_source_node mode l _ ctx.resources _
  change ByteMemory.bytesAt _ l.sourceNode (nodeBytes mode l.sourceNode _ _ _).length=nodeBytes mode l.sourceNode _ _ _ at current
  rw [node_length,ctx.nodeLocated] at current
  exact current

theorem other_current (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (query : Fin g.nodes) (different : query≠node) :
    ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory) (nodePC mode origin g query) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g query) (Listing8GraphNodeImage.value mode origin g query) := by
  have lower:=Listing8GraphLayout.node_lower mode origin g.transitions query.val
  change Listing8GraphLayout.input mode origin g.transitions≤nodePC mode origin g query at lower
  have after:=Nat.le_trans (call_before_input mode origin l t g node rule ctx) lower
  let fragment:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have endBefore : Listing8FailureLayout.endPC mode fragment≤nodePC mode origin g query := by
    change Listing8FailureLayout.callPC mode fragment+5≤nodePC mode origin g query at after
    dsimp only [Listing8FailureLayout.callPC] at after
    omega
  have startBefore : fragment.start≤nodePC mode origin g query := by
    have coords:=Listing8FailureLayout.positions mode fragment
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have regionOutside : fragment.start+(Listing8FailureLayout.bytes mode fragment).length≤nodePC mode origin g query := by
    rw [Listing8FailureLayout.bytes_length,←(Listing8FailureLayout.positions mode fragment).2.2.2.1]
    exact endBefore
  have callOutside : Listing8FailureLayout.callPC mode fragment+
      (Listing8FailureGlobalImage.callBytes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).length≤nodePC mode origin g query := by
    have size : (Listing8FailureGlobalImage.callBytes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).length=5 := by cases mode <;> rfl
    rw [size]
    exact after
  have sourceOutside : l.sourceNode+nodeSpan mode≤nodePC mode origin g query ∨ nodePC mode origin g query+nodeSpan mode≤l.sourceNode := by
    rw [ctx.nodeLocated]
    have distinct : query.val≠node.val := by intro same;exact different (Fin.ext same)
    rcases Nat.lt_or_gt_of_ne distinct with before | later
    · right;exact Listing8GraphLayout.nodes_apart mode origin g.transitions query.val node.val before
    · left;exact Listing8GraphLayout.nodes_apart mode origin g.transitions node.val query.val later
  have transitionOutside : l.sourceTransition+transitionSpan mode≤nodePC mode origin g query := by
    rw [ctx.ruleLocated]
    exact Listing8GraphLayout.table_node_apart mode origin g.transitions rule.val query.val rule.isLt
  rw [initialMemory,Listing8LateFrames.initial_image mode l t (values mode origin g node rule) _ _ ctx.resources ctx.body _ _ _
    startBefore
    sourceOutside (Or.inl transitionOutside),Listing8FailureGlobalImage.backing,
    Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl regionOutside),
    Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl callOutside),
    extra_window mode origin l t g node rule ctx memory _ _ lower]
  exact Listing8GraphNodeImage.current mode origin g query memory
end SmcTuring.Appendix.Listing8GraphInputInitial

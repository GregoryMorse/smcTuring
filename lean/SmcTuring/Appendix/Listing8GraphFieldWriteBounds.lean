module
public import SmcTuring.Appendix.Listing8GraphCopyWriteBounds
public import SmcTuring.Native.StringWrites

public section
namespace SmcTuring.Appendix.Listing8GraphFieldWriteBounds
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem node_word (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    StringWrites.WordOwned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Arithmetic.encodeNat mode (nodePC mode origin g index)) := by
  unfold StringWrites.WordOwned
  rw [Listing8GraphPointers.node_toNat mode origin g index bounds]
  have lower:=Nat.le_trans (Listing9EarlyImage.input_after_origin mode origin g.transitions)
    (Listing8GraphLayout.node_lower mode origin g.transitions index.val)
  have upper:=Listing8GraphLayout.node_upper mode origin g.transitions g.nodes index.val index.isLt
  change nodePC mode origin g index+nodeSpan mode≤_ at upper
  have size:=(Listing8CopyWriteBounds.spans mode).1
  exact ⟨lower,by omega⟩

theorem rule_word (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    StringWrites.WordOwned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Arithmetic.encodeNat mode (rulePC mode origin g index)) := by
  unfold StringWrites.WordOwned
  rw [Listing8GraphPointers.rule_toNat mode origin g index bounds]
  have lower:=Listing8GraphLayout.transition_lower mode origin index.val
  rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset] at lower
  change origin+(if mode=.x86 then 837 else 1310)≤rulePC mode origin g index at lower
  have upper:=Nat.le_trans (Listing8GraphLayout.transition_upper mode origin g.transitions index.val index.isLt)
    (Nat.le_trans (Listing8GraphLayout.table_before_input mode origin g.transitions) (Listing8LoopTailGeometry.input_before_end mode origin g))
  change rulePC mode origin g index+transitionSpan mode≤_ at upper
  have size:=(Listing8CopyWriteBounds.spans mode).2
  constructor
  · cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at lower <;> omega
  · omega

theorem state_word (mode : Mode) (origin : Nat) (g : Graph) (target : Option (Fin g.transitions))
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    StringWrites.WordOwned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Arithmetic.encodeNat mode (statePC mode origin g target)) := by
  cases target with
  | none => exact node_word mode origin g g.halt bounds
  | some index => exact rule_word mode origin g index bounds

theorem next_word (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    StringWrites.WordOwned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Arithmetic.encodeNat mode (nextPC mode origin g index)) := by
  unfold nextPC
  split_ifs with scan
  · exact rule_word mode origin g ⟨index.val+1,scan.2⟩ bounds
  · exact node_word mode origin g g.halt bounds

/-- Logical neighbor/rule labels derive every complete indirect reader
word bound inside the emitted graph; native future values are not supplied. -/
theorem graph_words (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    ∀ word∈[(values mode origin g node rule).back,(values mode origin g node rule).forward,
      (values mode origin g node rule).next,(values mode origin g node rule).newState],
      StringWrites.WordOwned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) word := by
  intro word member
  simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact node_word mode origin g (g.tape node).back bounds
  · exact node_word mode origin g (g.tape node).forward bounds
  · exact next_word mode origin g rule bounds
  · exact state_word mode origin g (g.rules rule).destination bounds

theorem input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    origin≤l.input.start ∧ Listing8LiteralInput.endPC mode l.input≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  have main:=(Listing8GraphCopyWriteBounds.lower mode origin l t g node rule ctx).1
  have positions:=Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined
  have body:=Listing8FailureGeometry.positions mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.body
  have call:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
    (Listing8LoopTailGeometry.input_before_end mode origin g)
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at positions body <;> constructor <;> omega

theorem direction (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    origin≤l.direction ∧ l.direction+10≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  have before:=(input mode origin l t g node rule ctx).1
  have inputPositions:=Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined
  have bodyPositions:=Listing8FailureGeometry.positions mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.body
  have call:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
    (Listing8LoopTailGeometry.input_before_end mode origin g)
  rw [ctx.body.state.head.direction]
  cases mode <;> simp [Listing8DirectionGeometry.region,Listing8DirectionLayout.directionPC,
    Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,
    Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,
    Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,
    Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at inputPositions bodyPositions ⊢ <;> constructor <;> omega

end SmcTuring.Appendix.Listing8GraphFieldWriteBounds

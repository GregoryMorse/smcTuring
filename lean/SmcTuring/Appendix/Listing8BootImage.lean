module
public import SmcTuring.Appendix.Listing4Entry
public import SmcTuring.Appendix.Listing8GlobalFailure
public import SmcTuring.Native.ByteOverlay

public section
namespace SmcTuring.Appendix.Listing8BootImage
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
structure Bounds (mode : Mode) (origin : Nat) (l : Layout) : Prop where
  packed : l.start=Listing4EntryLayout.mainPC mode origin
  node : l.sourceNode+nodeSpan mode ≤ origin ∨ l.start ≤ l.sourceNode
  transition : l.sourceTransition+transitionSpan mode ≤ origin ∨ l.start ≤ l.sourceTransition
@[expose] def beginPC (mode : Mode) (origin : Nat) := Listing4JumpLayout.beginPC mode origin
@[expose] def sites (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) : List ByteOverlay.Site :=
  [⟨Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin),Listing8FailureGlobalImage.callBytes mode l sentinel begin⟩,
   ⟨(Listing8FailureGeometry.region mode l sentinel begin).start,Listing8FailureLayout.bytes mode (Listing8FailureGeometry.region mode l sentinel begin)⟩,
   ⟨(Listing8StateGeometry.region mode l).start,Listing8StateLayout.bytes mode (Listing8StateGeometry.region mode l)⟩,
   ⟨(Listing8DirectionGeometry.region mode l).start,Listing8DirectionLayout.bytes mode (Listing8DirectionGeometry.region mode l)⟩,
   ⟨codeEnd mode l,Listing8PointerCopies.bytes mode l t⟩,
   ⟨l.input.start,inputBytes mode l⟩,⟨l.start,codeBytes mode l⟩,
   ⟨l.sourceNode,sourceNodeBytes mode l v⟩,⟨l.sourceTransition,sourceTransitionBytes mode l v⟩]
theorem memory_overlay (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (extra : ByteMemory.Memory) :
    Listing8FailureGlobalImage.memory mode l t v sentinel begin extra=ByteOverlay.run (sites mode l t v sentinel begin) extra := rfl

theorem separated (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (r : Resources mode l) (boot : Bounds mode origin l) (body : Listing8FailureGeometry.Bounds mode l t sentinel begin) :
    ∀ site∈sites mode l t v sentinel begin,
      origin+(Listing4EntryLayout.bytes mode origin).length ≤ site.pc ∨ site.pc+site.bytes.length ≤ origin := by
  have codeEnd := code_length mode l
  have beforeInput := r.inputAfter
  have input := Listing8InputBounds.positions mode l t body.state.head.input.fields body.state.head.input.joined
  have direction : (Listing8DirectionGeometry.region mode l).start=Listing8LiteralInput.endPC mode l.input := rfl
  have stateBefore := Listing8FailureFrames.state_before mode l sentinel begin
  have stateCoords := Listing8StateGeometry.positions mode l t body.state
  have bodyCoords := Listing8FailureGeometry.positions mode l t sentinel begin body
  have beforeState : l.start ≤ (Listing8StateGeometry.region mode l).start := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at stateCoords <;> omega
  have nodeLength : (sourceNodeBytes mode l v).length=nodeSpan mode := node_length mode _ _ _ _
  have transitionLength : (sourceTransitionBytes mode l v).length=transitionSpan mode := transition_length mode _ _ _ _ _ _
  have packed : origin+(Listing4EntryLayout.bytes mode origin).length=l.start := by
    rw [Listing4EntryLayout.bytes_length,boot.packed];rfl
  intro site member
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left;rw [packed]
    change l.start ≤ Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at bodyCoords <;> omega
  · left;rw [packed];exact Nat.le_trans beforeState stateBefore
  · exact Or.inl (by rw [packed];exact beforeState)
  · left;rw [packed,direction]
    change l.start ≤ Listing8LiteralInput.endPC mode l.input
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input <;> omega
  · left;rw [packed];change l.start ≤ Listing8CopyImage.codeEnd mode l;omega
  · left;rw [packed];change l.start ≤ l.input.start;omega
  · left;rw [packed]
  · rw [packed,nodeLength];exact Or.symm boot.node
  · rw [packed,transitionLength];exact Or.symm boot.transition

theorem memory_put (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (r : Resources mode l) (boot : Bounds mode origin l) (body : Listing8FailureGeometry.Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) :
    Listing8FailureGlobalImage.memory mode l t v sentinel begin (ByteMemory.putBytes extra origin (Listing4EntryLayout.bytes mode origin))=
      ByteMemory.putBytes (Listing8FailureGlobalImage.memory mode l t v sentinel begin extra) origin (Listing4EntryLayout.bytes mode origin) := by
  rw [memory_overlay,memory_overlay]
  exact ByteOverlay.run_put _ _ _ _ (separated mode origin l t v sentinel begin r boot body)
end SmcTuring.Appendix.Listing8BootImage

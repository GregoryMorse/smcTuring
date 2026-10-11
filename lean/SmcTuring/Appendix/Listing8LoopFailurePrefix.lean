module
public import SmcTuring.Appendix.Listing8LoopStateFrames
public import SmcTuring.Appendix.Listing8FailureReuseTransport

public section
namespace SmcTuring.Appendix.Listing8LoopFailurePrefix
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
structure Bounds (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) : Prop where
  state : Listing8LoopState.Bounds mode l t v
  failure : Listing8FailureGeometry.Bounds mode l t sentinel begin
/-- Both contracts describe the same present main-entry memory. Previous
failure mask/AND values are unrestricted by the reusable failure contract. -/
structure Current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput)
    (sentinel begin : Nat) (memory : ByteMemory.Memory) : Prop where
  state : Listing8LoopState.Current mode l t v old memory
  failure : Listing8FailureReuseImage.Current mode (Listing8FailureGeometry.region mode l sentinel begin) memory

theorem code_before (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l) (sentinel begin : Nat)
    (b : Listing8FailureGeometry.Bounds mode l t sentinel begin) (observed : Nat)
    (after : (Listing8FailureGeometry.region mode l sentinel begin).start≤observed) : codeEnd mode l≤observed := by
  have fail:=(Listing8FailureGeometry.positions mode l t sentinel begin b).1
  have input:=(Listing8InputBounds.positions mode l t b.state.head.input.fields b.state.head.input.joined).2.1
  have endInput:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  have before:=r.inputAfter
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at fail input endInput <;> omega

theorem prefix_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput)
    (sentinel begin : Nat) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (after : (Listing8FailureGeometry.region mode l sentinel begin).start≤observed) :
    ByteMemory.bytesAt (Listing8MainPrefix.finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  have bounds:=b.state.head.input.input.prefixBounds
  have codeBefore:=code_before mode l t bounds.resources sentinel begin b.failure observed after
  have stateBefore:=Listing8FailureFrames.state_before mode l sentinel begin
  have headAfter:=Nat.le_trans stateBefore after
  have fail:=(Listing8FailureGeometry.positions mode l t sentinel begin b.failure).1
  have input:=(Listing8InputBounds.positions mode l t b.failure.state.head.input.fields b.failure.state.head.input.joined).2.1
  have lower : Listing8LiteralInput.endPC mode l.input≤observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at fail input <;> omega
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have cursor:=Listing8PointerCopies.cursor_before mode l
  have d:=destinations mode l
  apply Listing8MainPrefixFrames.window mode l t v bounds state entry forward current.state.head.input.prefixCurrent observed count
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · intro site siteMember
    have bound:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site siteMember).2.1
    change site.owner+10≤codeEnd mode l at bound
    exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (Listing8StateGeometry.direction_outside mode l t b.failure.state observed headAfter)
  · exact Or.inl (by omega)
  · intro writer member
    exact Or.inl (Listing8FailureGeometry.pointer_outside mode l t sentinel begin b.failure observed after writer member)

theorem window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput)
    (sentinel begin : Nat) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (after : (Listing8FailureGeometry.region mode l sentinel begin).start≤observed)
    (upper : observed+count≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+5) :
    ByteMemory.bytesAt (Listing8LoopState.finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [Listing8LoopStateFrames.window mode l t v old b.state state entry forward current.state observed count
    (fun writer member => Or.inl (Nat.le_trans (Listing8FailureGeometry.state_helpers_before mode l sentinel begin writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8FailureGeometry.state_packets_before mode l t sentinel begin
      b.state.head.input.input.prefixBounds.resources b.failure writer member) after)),
    Listing8LoopStatePrefix.head_window mode l t v old b.state state entry forward current.state observed count
      (Nat.le_trans (Listing8FailureFrames.state_before mode l sentinel begin) after),
    Listing8MainInputFrames.input_window mode l t v old b.state.head.input state entry forward current.state.head.input observed count
      (Listing8FailureGeometry.input_outside mode l t sentinel begin b.failure observed count after upper)]
  exact prefix_window mode l t v old sentinel begin b state entry forward current observed count after

theorem current_after_state (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput)
    (sentinel begin : Nat) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory) :
    Listing8FailureReuseImage.Current mode (Listing8FailureGeometry.region mode l sentinel begin) (Listing8LoopState.finish mode l t v state).principal.memory := by
  apply Listing8FailureReuseTransport.current mode _ _ _ current.failure
  intro observed count after beforeEnd
  have before : Listing8FailureLayout.endPC mode (Listing8FailureGeometry.region mode l sentinel begin)≤
      Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+5 := by
    unfold Listing8FailureLayout.callPC;omega
  exact window mode l t v old sentinel begin b state entry forward current observed count after (Nat.le_trans beforeEnd before)

end SmcTuring.Appendix.Listing8LoopFailurePrefix

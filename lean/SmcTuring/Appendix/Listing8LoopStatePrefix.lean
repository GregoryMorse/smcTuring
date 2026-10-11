module
public import SmcTuring.Appendix.Listing8LoopHead
public import SmcTuring.Appendix.Listing8LoopStateImage
public import SmcTuring.Appendix.Listing8MainInputFrames

public section
namespace SmcTuring.Appendix.Listing8LoopStatePrefix
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
structure Bounds (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) : Prop where
  head : Listing8LoopHead.Bounds mode l t v
  state : Listing8StateGeometry.Bounds mode l t
structure Current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (memory : ByteMemory.Memory) : Prop where
  head : Listing8LoopHead.Current mode l t v old memory
  state : Listing8LoopStateImage.Current mode (Listing8StateGeometry.region mode l) memory

theorem code_before (mode : Mode) (l : Layout) (t : Targets) (r : Resources mode l) (b : Listing8StateGeometry.Bounds mode l t)
    (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) : codeEnd mode l≤w.1 := by
  have lower:=(Listing8StateGeometry.window_span mode (Listing8StateGeometry.region mode l) w member).1
  have state:=(Listing8StateGeometry.positions mode l t b).1
  have input:=(Listing8InputBounds.positions mode l t b.head.input.fields b.head.input.joined).2.1
  have after:=r.inputAfter
  have endInput:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at state input endInput <;> omega

theorem prefix_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory)
    (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8MainPrefix.finish mode l t v state).principal.memory w.1 w.2=ByteMemory.bytesAt state.principal.memory w.1 w.2 := by
  have bounds:=b.head.input.input.prefixBounds
  have codeBefore:=code_before mode l t bounds.resources b.state w member
  have spans:=Listing8StateGeometry.window_span mode (Listing8StateGeometry.region mode l) w member
  have coords:=(Listing8StateGeometry.positions mode l t b.state).1
  have input:=(Listing8InputBounds.positions mode l t b.state.head.input.fields b.state.head.input.joined).2.1
  have lower : Listing8LiteralInput.endPC mode l.input≤w.1 := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords input <;> omega
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have cursor:=Listing8PointerCopies.cursor_before mode l
  have d:=destinations mode l
  apply Listing8MainPrefixFrames.window mode l t v bounds state entry forward current.head.input.prefixCurrent w.1 w.2
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · intro site siteMember
    have bound:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site siteMember).2.1
    change site.owner+10≤codeEnd mode l at bound
    exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (Listing8StateGeometry.direction_outside mode l t b.state w.1 spans.1)
  · exact Or.inl (by omega)
  · exact Listing8StateGeometry.pointer_outside mode l t b.state w member

theorem head_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory)
    (observed count : Nat) (after : (Listing8StateGeometry.region mode l).start≤observed) :
    ByteMemory.bytesAt (Listing8LoopHead.finish mode l t v state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8MainInput.finish mode l t v state).principal.memory observed count := by
  rw [Listing8LoopHead.finish,Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t b.head.direction) _
    (Listing8LoopDirection.endpoint mode l t v old b.head state entry forward current.head) observed count
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.tail_xors mode l writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.tail_packets mode l t b.state writer (List.mem_append_left _ member)) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.tail_packets mode l t b.state writer (List.mem_append_right _ member)) after))]
  exact Listing8LoopDirection.window mode l t v old b.head state entry forward current.head observed count
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.direction_helpers mode l writer member) after))
    (fun writer member => Or.inl (Nat.le_trans (Listing8StateFrames.direction_packets mode l writer member) after))

theorem window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory)
    (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8LoopHead.finish mode l t v state).principal.memory w.1 w.2=ByteMemory.bytesAt state.principal.memory w.1 w.2 := by
  rw [head_window mode l t v old b state entry forward current w.1 w.2 (Listing8StateGeometry.window_span mode _ w member).1,
    Listing8MainInputFrames.input_window mode l t v old b.head.input state entry forward current.head.input _ _
      (Listing8StateGeometry.input_outside mode l t b.state w member)]
  exact prefix_window mode l t v old b state entry forward current w member

theorem current_after_head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    Listing8LoopStateImage.Current mode (Listing8StateGeometry.region mode l) (Listing8LoopHead.finish mode l t v state).principal.memory :=
  Listing8LoopStateImage.transport mode _ _ _ current.state (window mode l t v old b state entry forward current)

end SmcTuring.Appendix.Listing8LoopStatePrefix

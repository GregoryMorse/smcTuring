module
public import SmcTuring.Appendix.Listing8JointOriginalGraphInput
public import SmcTuring.Appendix.Listing8JointOriginalGraphMain

public section
namespace SmcTuring.Appendix.Listing8InactiveLocalCatalog
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
/-- All fixed direction/state windows and every subwindow of failure/CALL.
Operand masks are excluded from the first two inventories. -/
@[expose] def Windows (mode : Mode) (l : Layout) (sentinel begin : Nat) (w : Nat × Nat) : Prop :=
  w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l) ∨
  w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l) ∨
  ((Listing8FailureGeometry.region mode l sentinel begin).start≤w.1 ∧
    w.1+w.2≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+5)
@[expose] def Snapshot (mode : Mode) (l : Layout) (sentinel begin : Nat)
    (original memory : ByteMemory.Memory) : Prop :=
  ∀ w,Windows mode l sentinel begin w → ByteMemory.bytesAt memory w.1 w.2=ByteMemory.bytesAt original w.1 w.2
@[expose] def Outside (mode : Mode) (l : Layout) (sentinel begin address count : Nat) : Prop :=
  ∀ w,Windows mode l sentinel begin w → address+count≤w.1 ∨ w.1+w.2≤address

theorem geometry (mode : Mode) (l : Layout) (t : Targets) (sentinel begin : Nat)
    (bounds : Listing8FailureGeometry.Bounds mode l t sentinel begin) (w : Nat × Nat)
    (member : Windows mode l sentinel begin w) :
    Listing8LiteralInput.endPC mode l.input≤w.1 ∧ Listing8InputWindows.Outside mode l.input w.1 w.2 := by
  rcases member with head | state | failure
  · exact ⟨(Listing8DirectionWindows.window_span mode _ w head).1,
      Listing8DirectionPrefixFrames.input_outside mode l t bounds.state.head w head⟩
  · have span:=(Listing8StateGeometry.window_span mode _ w state).1
    have positions:=Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)
    have lower : Listing8LiteralInput.endPC mode l.input≤(Listing8StateGeometry.region mode l).start := by
      change Listing8LiteralInput.endPC mode l.input≤Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)
      have ending:=positions.2.2.2.2.2.2.2
      change Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)=
        Listing8LiteralInput.endPC mode l.input+(if mode=.x86 then 91 else 202) at ending
      omega
    exact ⟨lower.trans span,Listing8StateGeometry.input_outside mode l t bounds.state w state⟩
  · have coords:=Listing8FailureGeometry.positions mode l t sentinel begin bounds
    have input:=(Listing8InputBounds.positions mode l t bounds.state.head.input.fields bounds.state.head.input.joined).2.1
    refine ⟨?_,Listing8FailureGeometry.input_outside mode l t sentinel begin bounds w.1 w.2 failure.1 failure.2⟩
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords input <;> omega

/-- Complete stores, including temporary copy-helper writes, avoid the
combined fixed windows. Endpoint-only effect equations are not used here. -/
theorem fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing8InputTemplateRegions.Fields mode l.input
      (Outside mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) := by
  have internal:=Listing8LiteralComposition.field_bounds mode l.input
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have cursor:=Listing8InputBounds.cursor_bounds mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w member;exact (geometry mode l t _ _ ctx.body w member).2.scalar
  · intro w member;left;have lower:=(geometry mode l t _ _ ctx.body w member).1;omega
  · intro w member;exact (geometry mode l t _ _ ctx.body w member).2.mask
  · intro w member;exact (geometry mode l t _ _ ctx.body w member).2.pending
  · intro w member;left
    have lower:=(geometry mode l t _ _ ctx.body w member).1
    have ending:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [Mode.wordBytes,reduceCtorEq,ite_true,ite_false] at cursor ending ⊢ <;> omega
  · intro w member;exact (geometry mode l t _ _ ctx.body w member).2.tape
  · intro helper inside w member;exact (geometry mode l t _ _ ctx.body w member).2.destinations helper inside

theorem store (mode : Mode) (l : Layout) (sentinel begin : Nat) (original memory : ByteMemory.Memory)
    (address : Nat) (packet : List LittleEndian.Byte) (current : Snapshot mode l sentinel begin original memory)
    (outside : Outside mode l sentinel begin address packet.length) :
    Snapshot mode l sentinel begin original (ByteMemory.putBytes memory address packet) := by
  intro w member
  rw [ByteMemory.bytes_at_frame]
  · exact current w member
  · intro index inside
    have bound:=index.isLt
    unfold ByteMemory.Inside at inside
    rcases outside w member with early | late <;> omega

end SmcTuring.Appendix.Listing8InactiveLocalCatalog

module
public import SmcTuring.Appendix.Listing8GraphFieldWriteBounds

public section
namespace SmcTuring.Appendix.Listing8GraphPointerWriteBounds
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem word (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    (origin≤(Listing8PointerCopies.word mode l).source ∧ (Listing8PointerCopies.word mode l).source+mode.wordBytes≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes) ∧
    (origin≤(Listing8PointerCopies.word mode l).destination ∧ (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes) := by
  have placed:=Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx
  have coords:=coordinates mode l
  have destinations:=Listing8CopyImage.destinations mode l
  have before:=endpoint_lower mode l.start (nodeSpan mode)
  change l.start≤secondStart mode l at before
  have cursor:=Listing8PointerCopies.cursor_before mode l
  have block:=placed.block
  cases mode <;> simp [Listing8PointerCopies.word,pointerField,ReaderImage.labelOffset,Mode.wordBytes,
    transitionParams,Listing8ModeOffsets.transitionEntry,patchLayout,Listing8ModeOffsets.nodeEntry,
    nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,StringCodec.sourceField,StringCodec.fieldOffset] at destinations cursor ⊢ <;>
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

theorem dwords (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    ∀ lay∈Listing8PointerCopies.layouts mode l t,
      (origin≤lay.source ∧ lay.source+4≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes) ∧
      (origin≤lay.destination ∧ lay.destination+4≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes) := by
  have placed:=Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx
  have lower:=(Listing8GraphFieldWriteBounds.input mode origin l t g node rule ctx).1
  rw [ctx.body.state.head.input.joined] at lower
  have first:=endpoint_lower mode l.start (nodeSpan mode)
  change l.start≤secondStart mode l at first
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  have call:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
    (Listing8LoopTailGeometry.input_before_end mode origin g)
  have body:=Listing8FailureGeometry.positions mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.body
  have failureBefore : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤
      Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at body <;> omega
  intro lay member
  have source:=Listing8PointerCopies.source_bounds mode l t lay member
  have destination:=Listing8PointerCopies.destination_after mode l t ctx.copies lay member
  have upper:=Listing8FailureGeometry.pointer_outside mode l t _ _ ctx.body _ (Nat.le_refl _) lay member
  have block:=placed.block
  exact ⟨⟨by omega,by omega⟩,⟨Nat.le_trans lower destination,Nat.le_trans upper failureBefore⟩⟩

end SmcTuring.Appendix.Listing8GraphPointerWriteBounds

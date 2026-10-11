module
public import SmcTuring.Appendix.Listing8GlobalMainBounds
public import SmcTuring.Appendix.Listing8GraphPointerWrites
public import SmcTuring.Native.BoundedStoreRegions

public section
namespace SmcTuring.Appendix.Listing8GlobalPointerRegions
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem word (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    (Listing4EntryLayout.mainPC mode origin≤(Listing8PointerCopies.word mode l).source ∧ (Listing8PointerCopies.word mode l).source+mode.wordBytes≤Listing8JumpLayout.jumpPC mode origin) ∧
    (Listing4EntryLayout.mainPC mode origin≤(Listing8PointerCopies.word mode l).destination ∧ (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤Listing8JumpLayout.jumpPC mode origin) := by
  have coords:=coordinates mode l
  have destinations:=Listing8CopyImage.destinations mode l
  have before:=endpoint_lower mode l.start (nodeSpan mode)
  change l.start≤secondStart mode l at before
  have cursor:=Listing8PointerCopies.cursor_before mode l
  have block:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  cases mode <;> simp [Listing8PointerCopies.word,pointerField,ReaderImage.labelOffset,Mode.wordBytes,
    transitionParams,Listing8ModeOffsets.transitionEntry,patchLayout,Listing8ModeOffsets.nodeEntry,
    nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,StringCodec.sourceField,StringCodec.fieldOffset] at destinations cursor ⊢ <;>
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

theorem dwords (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    ∀ lay∈Listing8PointerCopies.layouts mode l t,
      (Listing4EntryLayout.mainPC mode origin≤lay.source ∧ lay.source+4≤Listing8JumpLayout.jumpPC mode origin) ∧
      (Listing4EntryLayout.mainPC mode origin≤lay.destination ∧ lay.destination+4≤Listing8JumpLayout.jumpPC mode origin) := by
  have lower:=(Listing8GlobalMainBounds.input mode origin l t g node rule ctx).1
  rw [ctx.body.state.head.input.joined] at lower
  have first:=endpoint_lower mode l.start (nodeSpan mode)
  change l.start≤secondStart mode l at first
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  have endAt:=(Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx).bodyEnd
  have body:=Listing8FailureGeometry.positions mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.body
  have failureBefore : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤
      Listing8JumpLayout.jumpPC mode origin := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at body <;> omega
  intro lay member
  have source:=Listing8PointerCopies.source_bounds mode l t lay member
  have destination:=Listing8PointerCopies.destination_after mode l t ctx.copies lay member
  have upper:=Listing8FailureGeometry.pointer_outside mode l t _ _ ctx.body _ (Nat.le_refl _) lay member
  have block:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  exact ⟨⟨by omega,by omega⟩,⟨Nat.le_trans lower destination,Nat.le_trans upper failureBefore⟩⟩


theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (codeEnd mode l)) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)) state := by
  have fields:=word mode origin l t g node rule ctx
  have first:=StringCopyWrites.word mode (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin)
    (Listing8PointerCopies.word mode l) ctx.copies.wordValid state entry fields.1 fields.2
  have next : (StringDwordCopy.wordFinish mode (Listing8PointerCopies.word mode l) state).principal.pc=
      Arithmetic.encodeNat mode (Listing8PointerCopies.dwordStart mode l) := by
    change (ConversionEffects.finish mode (Listing8PointerCopies.word mode l) state.principal).pc=_
    rw [ConversionEffects.effect mode (Listing8PointerCopies.word mode l) ctx.copies.wordValid state.principal entry]
    rfl
  have last:=StringSequenceWrites.owned mode (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin)
    (Listing8PointerCopies.layouts mode l t) _ (Listing8PointerCopies.chain mode l t) ctx.copies.dwordValid
    (dwords mode origin l t g node rule ctx) _ next
  apply BoundedStoreRegions.interval mode _ (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin)
    _ state (fun _ _ lower upper => Or.inr (Or.inl ⟨lower,upper⟩))
  rw [Listing8PointerCopies.program,List.map_append,StringWrites.owned_run_append,StringSequenceWrites.word_run]
  exact ⟨first,last⟩

end SmcTuring.Appendix.Listing8GlobalPointerRegions

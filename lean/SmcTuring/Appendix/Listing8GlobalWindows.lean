module
public import SmcTuring.Appendix.Listing8GlobalInput
public import SmcTuring.Appendix.Listing8InputWindows

public section
namespace SmcTuring.Appendix.Listing8GlobalWindows
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets := Listing8PointerCopies.Targets

theorem owners (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (afterInput : Listing8LiteralInput.endPC mode l.input ≤ observed)
    (direction : l.direction+10 ≤ observed ∨ observed+count ≤ l.direction+6) :
    ByteMemory.bytesAt (Listing8CopiedOwners.finish mode l v extra seed).principal.memory observed count =
      ByteMemory.bytesAt (image mode l v extra) observed count := by
  have lower : codeEnd mode l ≤ observed := by
    have after := r.inputAfter
    have endpoint := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at endpoint <;> omega
  have inputFields := Listing8CopiedOwners.scalar_bounds mode l
  have sourceField := Listing8OwnerImage.source_field_bounds mode l
  have inputEnd : l.input.start ≤ Listing8LiteralInput.endPC mode l.input := by
    have h := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at h <;> omega
  rw [(Listing8CopiedOwners.result mode l v r b extra seed).2.1]
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ direction,
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl (by omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl (by omega))]
  have patches : ∀ site ∈ Listing8ModeOffsets.sites mode (patchLayout mode l),
      site.owner+6 ≤ observed ∨ observed+count ≤ site.owner+2 := by
    intro site member
    simp only [Listing8ModeOffsets.sites,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> left <;>
      cases mode <;> simp [patchLayout,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,
        codeEnd,Listing8ModeOffsets.endPC,directionEntry,newEntry,currentEntry,nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize] at lower ⊢ <;> omega
  rw [Listing8OwnerImage.frame mode l v r b.tapeReach extra seed observed count patches (Or.inl (by omega)),
    Listing8CopyTrace.second_effect mode l v r extra seed,Listing8CopyTrace.first_effect mode l v r extra seed]
  have nodeLength : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have transLength : (sourceTransitionBytes mode l v).length = transitionSpan mode := transition_length mode _ _ _ _ _ _
  rw [byte_frame _ _ _ _ _ (Or.inl (by rw [transLength];have d := (destinations mode l).2.2;omega)),
    byte_frame _ _ _ _ _ (Or.inl (by rw [nodeLength];have d := destinations mode l;omega))]
  rfl

theorem pointers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (afterInput : Listing8LiteralInput.endPC mode l.input ≤ observed)
    (direction : l.direction+10 ≤ observed ∨ observed+count ≤ l.direction+6)
    (targets : ∀ helper ∈ Listing8PointerCopies.layouts mode l t,
      helper.destination+4 ≤ observed ∨ observed+count ≤ helper.destination) :
    ByteMemory.bytesAt (Listing8PointerImage.finish mode l t v extra seed).principal.memory observed count =
      ByteMemory.bytesAt (image mode l v (Listing8PointerImage.backing mode l t extra)) observed count := by
  have codeBefore : codeEnd mode l ≤ observed := by
    have inputEnd := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    have after := r.inputAfter
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at inputEnd <;> omega
  have cursorBefore := Listing8PointerCopies.cursor_before mode l
  have priorEntry := (Listing8CopiedOwners.result mode l v r b (Listing8PointerImage.backing mode l t extra) seed).1
  rw [Listing8PointerImage.finish,Listing8PointerImage.ownerFinish,Listing8PointerCopies.window_frame mode l t copies _ priorEntry observed count
    (Or.inl (by omega)) targets]
  exact owners mode l v r b (Listing8PointerImage.backing mode l t extra) seed observed count afterInput direction

theorem input (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8GlobalInput.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (outside : Listing8InputWindows.Outside mode l.input observed count) :
    ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v extra seed).principal.memory observed count =
      ByteMemory.bytesAt (Listing8GlobalInput.entryState mode l t v extra seed).principal.memory observed count :=
  Listing8InputWindows.window mode l.input v.rule v.tape force v.fresh force r.inputFits
    (Listing8InputBounds.masks mode l bounds.fields)
    (Listing8InputBounds.update mode l t bounds.fields bounds.joined r)
    (Listing8InputBounds.outside mode l t bounds.fields bounds.joined r)
    (Listing8GlobalInput.entryState mode l t v extra seed).principal
    (Listing8GlobalInput.entry mode l t v r owners copies bounds extra seed)
    (Listing8GlobalInput.input_image mode l t v r owners copies bounds extra seed)
    (Listing8GlobalInput.cursor mode l t v r owners copies bounds extra seed)
    (Listing8GlobalInput.symbol mode l t v r owners copies bounds extra seed) observed count outside

end SmcTuring.Appendix.Listing8GlobalWindows

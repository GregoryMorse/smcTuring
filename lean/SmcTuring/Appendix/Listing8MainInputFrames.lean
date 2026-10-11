module
public import SmcTuring.Appendix.Listing8MainInput
public import SmcTuring.Appendix.Listing8InputWindows

public section
namespace SmcTuring.Appendix.Listing8MainInputFrames
open Native Listing8CopyImage Listing8MainInput

theorem input_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (observed count : Nat)
    (disjoint : Listing8InputWindows.Outside mode l.input observed count) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8MainPrefix.finish mode l t v state).principal.memory observed count := by
  have bounds:=b.input.prefixBounds
  exact Listing8InputWindows.window mode l.input v.rule v.tape old.pending v.fresh old.mask
    bounds.resources.inputFits (Listing8InputBounds.masks mode l bounds.fields)
    (Listing8InputBounds.update mode l t bounds.fields bounds.joined bounds.resources)
    (Listing8InputBounds.outside mode l t bounds.fields bounds.joined bounds.resources) _
    (Listing8MainPrefix.entry mode l t v bounds state entry forward current.prefixCurrent)
    (Listing8MainInputImage.current mode l t v old b.input state entry forward current)
    (Listing8MainPrefixFrames.head_cursor mode l t v bounds state entry forward current.prefixCurrent)
    (Listing8MainPrefixSources.tape_symbol mode l t v bounds b.pointersOutside state entry forward current.prefixCurrent)
    observed count disjoint

/-- The complete generic prefix/input execution preserves any early code
window apart from the explicitly written next-state cursor. -/
theorem before_patch (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (observed count : Nat)
    (after : l.start≤observed) (before : observed+count≤patchStart mode l+40)
    (cursor : (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤observed ∨ observed+count≤(Listing8PointerCopies.word mode l).destination) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  have bounds:=b.input.prefixBounds
  have inputAfter:=bounds.resources.inputAfter
  have d:=destinations mode l
  have nodeStart : (nodeParams mode l).destination=patchStart mode l+40 := rfl
  have fields:=Listing8LiteralComposition.field_bounds mode l.input
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have large : 10≤Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  rw [input_window mode l t v old b state entry forward current observed count
    ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega),?_,fun writer member => Or.inr (by
      have lower:=bounds.fields.masksAfter writer member;omega)⟩]
  · exact Listing8MainPrefixFrames.before_patch mode l t v bounds state entry forward current.prefixCurrent observed count before cursor
  · rw [bounds.fields.headLabel]
    rcases bounds.resources.nodeOutside with early | late
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- The actual head operand is retained through the generic input phase. -/
theorem head_cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    MixedMemory.getWord mode (finish mode l t v state).principal.memory l.input.cursor=Arithmetic.encodeNat mode l.input.head := by
  have bounds:=b.input.prefixBounds
  have firstBody : StringCodec.bodyStart mode l.start≤secondStart mode l := by
    unfold secondStart StringCodec.endpoint StringCodec.bodyEnd;omega
  have endFirst:=StringCodec.field_end mode l.start
  have secondStart : secondStart mode l≤(Listing8PointerCopies.word mode l).destination := by
    simp only [Listing8PointerCopies.word,StringCodec.sourceField];omega
  have before:=cursor_end mode l
  have after : l.start≤StringCodec.sourceField mode l.start := by simp only [StringCodec.sourceField];omega
  rw [bounds.fields.cursorLabel,bounds.fields.headLabel]
  unfold MixedMemory.getWord
  rw [before_patch mode l t v old b state entry forward current _ _ after (by omega)
    (Or.inr (by unfold StringCodec.bodyStart at firstBody;omega))]
  exact current.prefixCurrent.copying.nodeMacro.source

theorem patches_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory (patchStart mode l) (patchBytes mode l).length=patchBytes mode l := by
  have length : (patchBytes mode l).length=40 := by
    rw [patchBytes,DwordRetargetSequence.bytes_length,Listing8ModeOffsets.sites_length]
  have first:=endpoint_lower mode l.start (Listing8Prototypes.nodeSpan mode)
  have second:=endpoint_lower mode (secondStart mode l) (Listing8Prototypes.transitionSpan mode)
  change l.start≤secondStart mode l at first
  change secondStart mode l≤patchStart mode l at second
  rw [before_patch mode l t v old b state entry forward current _ _ (by omega) (by rw [length])
    (Or.inl (Listing8PointerCopies.cursor_before_patch mode l))]
  exact current.prefixCurrent.copying.patches

end SmcTuring.Appendix.Listing8MainInputFrames

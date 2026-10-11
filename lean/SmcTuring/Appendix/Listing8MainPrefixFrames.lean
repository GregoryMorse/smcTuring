module
public import SmcTuring.Appendix.Listing8MainPrefix

public section
namespace SmcTuring.Appendix.Listing8MainPrefixFrames
open Native Listing8CopyImage Listing8Prototypes Listing8MainPrefix

theorem window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) (observed count : Nat)
    (nodeOutside : (nodeParams mode l).destination+nodeSpan mode≤observed ∨ observed+count≤(nodeParams mode l).destination)
    (ruleOutside : (transitionParams mode l).destination+transitionSpan mode≤observed ∨ observed+count≤(transitionParams mode l).destination)
    (patches : ∀ site∈Listing8ModeOffsets.sites mode (patchLayout mode l),site.owner+6≤observed ∨ observed+count≤site.owner+2)
    (tape : Listing8LiteralInput.sourceField mode l.input+4≤observed ∨ observed+count≤Listing8LiteralInput.sourceField mode l.input)
    (ruleField : Listing8LiteralInput.scalarField mode l.input+4≤observed ∨ observed+count≤Listing8LiteralInput.scalarField mode l.input)
    (fresh : Listing8LiteralInput.updateStart mode l.input+10≤observed ∨ observed+count≤Listing8LiteralInput.updateStart mode l.input+6)
    (direction : l.direction+10≤observed ∨ observed+count≤l.direction+6)
    (cursor : (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤observed ∨ observed+count≤(Listing8PointerCopies.word mode l).destination)
    (pointers : ∀ writer∈Listing8PointerCopies.layouts mode l t,writer.destination+4≤observed ∨ observed+count≤writer.destination) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  change ByteMemory.bytesAt (Listing8PointerCopies.finish mode l t (Listing8MainLiveOwners.finish mode l v state)).principal.memory _ _=_
  rw [Listing8PointerCopies.window_frame mode l t b.copies _
    (Listing8MainLiveOwners.registers mode l v b.resources b.owners b.tapeReach state entry forward current.copying).1
    observed count cursor pointers]
  exact Listing8MainLiveOwners.window mode l v b.resources b.owners b.tapeReach state entry forward current.copying
    observed count nodeOutside ruleOutside patches tape ruleField fresh direction

/-- Every immutable header, macro suffix and patch packet before the
copied destinations survives; only the actual next-state cursor is excepted. -/
theorem before_patch (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) (observed count : Nat)
    (before : observed+count≤patchStart mode l+40)
    (cursor : (Listing8PointerCopies.word mode l).destination+mode.wordBytes≤observed ∨ observed+count≤(Listing8PointerCopies.word mode l).destination) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  have d:=destinations mode l
  have nodeStart : (nodeParams mode l).destination=patchStart mode l+40 := rfl
  have later : (nodeParams mode l).destination≤(transitionParams mode l).destination := by omega
  have inputAfter:=b.resources.inputAfter
  have ptrEnd : codeEnd mode l≤Listing8PointerCopies.endPC mode l := by have e:=(Listing8PointerCopies.sizes mode l t).2.1;omega
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have direction:=b.owners.directionAfter
  apply window mode l t v b state entry forward current observed count
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · intro site member
    have after:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).1
    change patchStart mode l+40≤site.owner at after
    exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · exact cursor
  · intro writer member
    exact Or.inr (by have after:=Listing8PointerCopies.destination_after mode l t b.copies writer member;omega)

theorem head_cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) :
    MixedMemory.getWord mode (finish mode l t v state).principal.memory l.input.cursor=Arithmetic.encodeNat mode l.input.head := by
  have firstBody : StringCodec.bodyStart mode l.start≤secondStart mode l := by
    unfold secondStart StringCodec.endpoint StringCodec.bodyEnd;omega
  have endFirst:=StringCodec.field_end mode l.start
  have secondStart : secondStart mode l≤(Listing8PointerCopies.word mode l).destination := by
    simp only [Listing8PointerCopies.word,StringCodec.sourceField];omega
  have before:=cursor_end mode l
  rw [b.fields.cursorLabel,b.fields.headLabel]
  unfold MixedMemory.getWord
  rw [before_patch mode l t v b state entry forward current (StringCodec.sourceField mode l.start) mode.wordBytes
    (by omega) (Or.inr (by unfold StringCodec.bodyStart at firstBody;omega))]
  exact current.copying.nodeMacro.source

theorem patches_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v state.principal.memory) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory (patchStart mode l) (patchBytes mode l).length=patchBytes mode l := by
  have length : (patchBytes mode l).length=40 := by
    rw [patchBytes,DwordRetargetSequence.bytes_length,Listing8ModeOffsets.sites_length]
  rw [before_patch mode l t v b state entry forward current _ _ (by rw [length])
    (Or.inl (Listing8PointerCopies.cursor_before_patch mode l))]
  exact current.copying.patches

end SmcTuring.Appendix.Listing8MainPrefixFrames

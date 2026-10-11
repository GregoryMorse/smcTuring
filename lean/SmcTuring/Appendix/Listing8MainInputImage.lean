module
public import SmcTuring.Appendix.Listing8MainPrefixFrames
public import SmcTuring.Appendix.Listing8OwnerInput
public import SmcTuring.Appendix.Listing8InputFields

public section
namespace SmcTuring.Appendix.Listing8MainInputImage
open Native Listing8CopyImage Listing8MainPrefix
abbrev Dword:=BitVec 32

/-- Arbitrary live values retained from the preceding invocation. -/
structure OldInput where
  rule : Dword
  tape : Dword
  pending : Dword
  fresh : Dword
  mask : Dword

/-- A present main-entry contract, including the entire previous input image.
It neither initializes replacement memory nor assumes a later input image. -/
structure Current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (memory : ByteMemory.Memory) : Prop where
  prefixCurrent : Listing8MainPrefix.Current mode l t v memory
  input : Listing8InputMask.Intact mode l.input old.rule old.tape old.pending old.fresh old.mask memory

structure Bounds (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) : Prop where
  prefixBounds : Listing8MainPrefix.Bounds mode l t v
  targetsAfter : ∀ pc∈[t.state,t.back,t.forward],Listing8LiteralInput.endPC mode l.input≤pc

theorem after_copies (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    Listing8InputMask.Intact mode l.input old.rule old.tape old.pending old.fresh old.mask
      (Listing8MainCopies.finish mode l state).principal.memory := by
  rw [Listing8InputMask.Intact,Listing8MainCopies.exterior_window mode l v b.prefixBounds.resources state entry forward
    current.prefixCurrent.copying l.input.start _ (Or.inr b.prefixBounds.resources.inputAfter)]
  exact current.input

theorem after_retargets (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    Listing8InputMask.Intact mode l.input old.rule v.tape old.pending old.fresh old.mask
      (Listing8MainRetarget.finish mode l v state).principal.memory := by
  have original:=after_copies mode l t v old b state entry forward current
  have kept : Listing8InputMask.Intact mode l.input old.rule old.tape old.pending old.fresh old.mask
      (DwordRetargetSequence.writes mode (Listing8ModeOffsets.sites mode (patchLayout mode l))
        (Listing8MainCopies.finish mode l state).principal.memory) := by
    rw [Listing8InputMask.Intact,DwordRetargetSequence.writes_window]
    · exact original
    · intro site member
      left
      have bounds:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).2.1
      change site.owner+10≤codeEnd mode l at bounds
      have after:=b.prefixBounds.resources.inputAfter
      omega
  rw [Listing8MainRetarget.effect mode l v b.prefixBounds.resources b.prefixBounds.tapeReach state entry forward current.prefixCurrent.copying]
  exact Listing8InputFields.tape_patch mode l.input _ _ v.tape _ _ _ _ kept

theorem after_owners (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    Listing8InputMask.Intact mode l.input v.rule v.tape old.pending v.fresh old.mask
      (Listing8MainLiveOwners.finish mode l v state).principal.memory := by
  have previous:=after_retargets mode l t v old b state entry forward current
  have rulePatch:=Listing8OwnerInput.rule_patch mode l.input _ v.rule _ _ _ _ _ previous
  have freshPatch:=Listing8OwnerInput.fresh_patch mode l.input _ _ _ _ v.fresh _ _ rulePatch
  rw [Listing8InputMask.Intact,(Listing8MainLiveOwners.result mode l v b.prefixBounds.resources b.prefixBounds.owners b.prefixBounds.tapeReach
    state entry forward current.prefixCurrent.copying).2.1,DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by
      have length:=Listing8InputMask.bytes_length mode l.input v.rule v.tape old.pending v.fresh old.mask
      have after:=b.prefixBounds.owners.directionAfter;omega))]
  exact freshPatch

/-- The whole ready-to-execute input image follows from the actual generic
prefix, with arbitrary prior pending/scalar/mask values overwritten in order. -/
theorem current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (image : Current mode l t v old state.principal.memory) :
    Listing8InputMask.Intact mode l.input v.rule v.tape old.pending v.fresh old.mask
      (Listing8MainPrefix.finish mode l t v state).principal.memory := by
  have previous:=after_owners mode l t v old b state entry forward image
  change ByteMemory.bytesAt (Listing8PointerCopies.finish mode l t (Listing8MainLiveOwners.finish mode l v state)).principal.memory
    l.input.start _=_
  rw [Listing8PointerCopies.window_frame mode l t b.prefixBounds.copies _
    (Listing8MainLiveOwners.registers mode l v b.prefixBounds.resources b.prefixBounds.owners b.prefixBounds.tapeReach
      state entry forward image.prefixCurrent.copying).1]
  · exact previous
  · left
    have cursor:=Listing8PointerCopies.cursor_before mode l
    have after:=b.prefixBounds.resources.inputAfter;omega
  · intro writer member
    have a:=b.targetsAfter t.state (by simp)
    have c:=b.targetsAfter t.back (by simp)
    have d:=b.targetsAfter t.forward (by simp)
    have extent:=Listing8InputMask.bytes_length mode l.input v.rule v.tape old.pending v.fresh old.mask
    right
    cases mode
    all_goals simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only
    all_goals omega

end SmcTuring.Appendix.Listing8MainInputImage

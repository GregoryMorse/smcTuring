module
public import SmcTuring.Appendix.Listing8Initializer
public import SmcTuring.Appendix.Listing8OwnerSequence

public section
namespace SmcTuring.Appendix.Listing8OwnerImage
open Native Listing8Prototypes Listing8CopyImage
abbrev Owner := Listing8OwnerSequence.Owner

@[expose] def owners (mode : Mode) (l : Layout) (v : Values mode) : List (Owner mode) :=
  [.pointer (backEntry mode l.sourceNode) (backEntry mode (nodeParams mode l).destination) v.back,
   .pointer (forwardEntry mode l.sourceNode) (forwardEntry mode (nodeParams mode l).destination) v.forward,
   .pointer l.sourceTransition (transitionParams mode l).destination v.next,
   .scalar (currentEntry mode (transitionParams mode l).destination) (Listing8LiteralInput.scalarField mode l.input) v.rule,
   .scalar (newEntry mode (transitionParams mode l).destination) (Listing8LiteralInput.updateStart mode l.input+6) v.fresh,
   .scalar (directionEntry mode (transitionParams mode l).destination) (l.direction+6) v.direction,
   .pointer (stateEntry mode l.sourceTransition) (stateEntry mode (transitionParams mode l).destination) v.newState]
@[expose] def pointerPositions (mode : Mode) (l : Layout) :=
  [backEntry mode (nodeParams mode l).destination,forwardEntry mode (nodeParams mode l).destination,
    (transitionParams mode l).destination,stateEntry mode (transitionParams mode l).destination]
@[expose] def state (mode : Mode) (l : Layout) (v : Values mode) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8Initializer.finish mode l v (initial mode l v backing seed)

theorem source_field_bounds (mode : Mode) (l : Layout) :
    l.input.start ≤ Listing8LiteralInput.sourceField mode l.input ∧
    Listing8LiteralInput.sourceField mode l.input+4 ≤ Listing8LiteralInput.endPC mode l.input := by
  have source := (Listing8LiteralInput.positions mode l.input).2.2.1
  have ending := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at source ending <;> omega

theorem source_field_fits (mode : Mode) (l : Layout) (r : Resources mode l) :
    Listing8LiteralInput.sourceField mode l.input < 2^(8*mode.wordBytes) := by
  have bounds := source_field_bounds mode l
  have fits := r.inputFits
  omega

theorem entry (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode = .x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (state mode l v backing seed).principal.pc = Arithmetic.encodeNat mode (backEntry mode (nodeParams mode l).destination) := by
  rw [state,Listing8Initializer.principal_effect,
    Listing8ModeOffsets.tape_owner_effect mode (patchLayout mode l) v.tape (block_capacity mode l r)
      (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)) reach (source_field_fits mode l r) _
      (Listing8CopyTrace.patch_entry mode l v r backing seed)]
  rfl

theorem frame (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode = .x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat)
    (patches : ∀ site ∈ Listing8ModeOffsets.sites mode (patchLayout mode l), site.owner+6 ≤ observed ∨ observed+count ≤ site.owner+2)
    (tape : Listing8LiteralInput.sourceField mode l.input+4 ≤ observed ∨ observed+count ≤ Listing8LiteralInput.sourceField mode l.input) :
    ByteMemory.bytesAt (state mode l v backing seed).principal.memory observed count =
      ByteMemory.bytesAt (Listing8CopyTrace.both mode l (initial mode l v backing seed)).principal.memory observed count := by
  rw [state,Listing8Initializer.principal_effect,
    Listing8ModeOffsets.tape_owner_effect mode (patchLayout mode l) v.tape (block_capacity mode l r)
      (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)) reach (source_field_fits mode l r) _
      (Listing8CopyTrace.patch_entry mode l v r backing seed)]
  change ByteMemory.bytesAt (ByteMemory.putBytes (DwordRetargetSequence.writes mode (Listing8ModeOffsets.sites mode (patchLayout mode l))
    (Listing8CopyTrace.both mode l (initial mode l v backing seed)).principal.memory)
    (Listing8LiteralInput.sourceField mode l.input) (LittleEndian.wordEncode 4 v.tape)) observed count = _
  rw [byte_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using tape),
    DwordRetargetSequence.writes_window mode _ _ observed count patches]

theorem pointer_bounds (mode : Mode) (l : Layout) (q : Nat) (member : q ∈ pointerPositions mode l) :
    l.start ≤ q ∧ q+pointerSpan mode ≤ codeEnd mode l := by
  have before := endpoint_lower mode l.start (nodeSpan mode)
  have next := endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change l.start ≤ secondStart mode l at before
  change secondStart mode l ≤ patchStart mode l at next
  simp only [pointerPositions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    cases mode <;> simp [backEntry,forwardEntry,stateEntry,directionEntry,newEntry,currentEntry,nodeParams,transitionParams,
      Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,Listing8ModeOffsets.endPC,
      patchLayout,codeEnd,nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,Nat.add_assoc] <;> omega

theorem pointer_patch_frame (mode : Mode) (l : Layout) (q : Nat) (member : q ∈ pointerPositions mode l)
    (site : DwordRetargetSequence.Site) (siteMember : site ∈ Listing8ModeOffsets.sites mode (patchLayout mode l)) :
    site.owner+6 ≤ q ∨ q+pointerSpan mode ≤ site.owner+2 := by
  simp only [pointerPositions,List.mem_cons,List.not_mem_nil,or_false] at member
  simp only [Listing8ModeOffsets.sites,List.mem_cons,List.not_mem_nil,or_false] at siteMember
  rcases member with rfl | rfl | rfl | rfl <;>
    rcases siteMember with rfl | rfl | rfl | rfl <;>
      cases mode <;> simp [nodeParams,transitionParams,backEntry,forwardEntry,stateEntry,directionEntry,newEntry,currentEntry,
        Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,patchLayout,nodeSpan,pointerSpan,ReaderImage.totalSize]

theorem pointer_frame (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode = .x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) (q : Nat) (member : q ∈ pointerPositions mode l) :
    ByteMemory.bytesAt (state mode l v backing seed).principal.memory q (pointerSpan mode) =
      ByteMemory.bytesAt (Listing8CopyTrace.both mode l (initial mode l v backing seed)).principal.memory q (pointerSpan mode) := by
  apply frame mode l v r reach backing seed q (pointerSpan mode)
  · exact pointer_patch_frame mode l q member
  · right
    have bound := pointer_bounds mode l q member
    have inputAfter := r.inputAfter
    have source := source_field_bounds mode l
    omega

theorem original_frame (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode = .x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) (q count : Nat)
    (outside : q+count ≤ l.start ∨ Listing8LiteralInput.endPC mode l.input ≤ q) :
    ByteMemory.bytesAt (state mode l v backing seed).principal.memory q count =
      ByteMemory.bytesAt (Listing8CopyTrace.both mode l (initial mode l v backing seed)).principal.memory q count := by
  have before := endpoint_lower mode l.start (nodeSpan mode)
  have next := endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change l.start ≤ secondStart mode l at before
  change secondStart mode l ≤ patchStart mode l at next
  have endBound := code_to_input mode l r
  have startBound : l.start ≤ l.input.start := by
    have d := destinations mode l
    have afterInput := r.inputAfter
    omega
  apply frame mode l v r reach backing seed q count
  · intro site member
    have bounds := Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member
    change patchStart mode l+40 ≤ site.owner ∧ site.owner+10 ≤ codeEnd mode l ∧ _ at bounds
    rcases outside with early | late <;> omega
  · have bounds := source_field_bounds mode l
    rcases outside with early | late <;> omega

theorem source_transition_after_copies (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8CopyTrace.both mode l (initial mode l v backing seed)).principal.memory l.sourceTransition
      (sourceTransitionBytes mode l v).length = sourceTransitionBytes mode l v := by
  have d := destinations mode l
  have ending := code_to_input mode l r
  have nlen : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have tlen : (sourceTransitionBytes mode l v).length = transitionSpan mode := transition_length mode _ _ _ _ _ _
  have a : (nodeParams mode l).destination+(sourceNodeBytes mode l v).length ≤ l.sourceTransition ∨
      l.sourceTransition+(sourceTransitionBytes mode l v).length ≤ (nodeParams mode l).destination := by
    rw [nlen,tlen]
    rcases r.transitionOutside with before | after <;> omega
  have b : (transitionParams mode l).destination+(sourceTransitionBytes mode l v).length ≤ l.sourceTransition ∨
      l.sourceTransition+(sourceTransitionBytes mode l v).length ≤ (transitionParams mode l).destination := by
    rw [tlen]
    rcases r.transitionOutside with before | after <;> omega
  rw [Listing8CopyTrace.second_effect mode l v r backing seed,byte_frame _ _ _ _ _ b,
    Listing8CopyTrace.first_effect mode l v r backing seed,byte_frame _ _ _ _ _ a]
  exact initial_source_transition mode l v backing

theorem original_node (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode = .x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (state mode l v backing seed).principal.memory l.sourceNode (sourceNodeBytes mode l v).length = sourceNodeBytes mode l v := by
  rw [original_frame mode l v r reach backing seed _ _ (by simpa only [sourceNodeBytes,node_length] using r.nodeOutside)]
  exact Listing8CopyTrace.source_node_retained mode l v r backing seed

theorem original_transition (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode = .x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (state mode l v backing seed).principal.memory l.sourceTransition (sourceTransitionBytes mode l v).length = sourceTransitionBytes mode l v := by
  rw [original_frame mode l v r reach backing seed _ _ (by simpa only [sourceTransitionBytes,transition_length] using r.transitionOutside)]
  exact source_transition_after_copies mode l v r backing seed

/-- Byte-window identities for source-addressed prototypes copied to any
physical entry. The original absolute address bytes are retained verbatim. -/
theorem node_windows (mode : Mode) (source copied : Nat) (symbol : BitVec 32) (back forward : Word mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory copied (nodeBytes mode source symbol back forward).length = nodeBytes mode source symbol back forward) :
    ByteMemory.bytesAt memory (backEntry mode copied) (pointerBytes mode (backEntry mode source) back).length = pointerBytes mode (backEntry mode source) back ∧
    ByteMemory.bytesAt memory (forwardEntry mode copied) (pointerBytes mode (forwardEntry mode source) forward).length = pointerBytes mode (forwardEntry mode source) forward := by
  have a := ByteWindow.packet memory copied (DwordOwner.bytes mode source symbol)
    (pointerBytes mode (backEntry mode source) back) (pointerBytes mode (forwardEntry mode source) forward) (by simpa [nodeBytes,List.append_assoc] using current)
  have b := ByteWindow.packet memory copied (DwordOwner.bytes mode source symbol ++ pointerBytes mode (backEntry mode source) back)
    (pointerBytes mode (forwardEntry mode source) forward) [] (by simpa [nodeBytes,List.append_assoc] using current)
  exact ⟨by simpa only [DwordOwner.length,backEntry] using a,
    by simpa only [List.length_append,DwordOwner.length,pointer_length,forwardEntry,backEntry,Nat.add_assoc] using b⟩

theorem transition_windows (mode : Mode) (source copied : Nat) (next newState : Word mode) (rule fresh direction : BitVec 32) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory copied (transitionBytes mode source next newState rule fresh direction).length = transitionBytes mode source next newState rule fresh direction) :
    ByteMemory.bytesAt memory copied (pointerBytes mode source next).length = pointerBytes mode source next ∧
    ByteMemory.bytesAt memory (stateEntry mode copied) (pointerBytes mode (stateEntry mode source) newState).length = pointerBytes mode (stateEntry mode source) newState := by
  have a := ByteWindow.packet memory copied [] (pointerBytes mode source next)
    (DwordOwner.bytes mode (currentEntry mode source) rule ++ DwordOwner.bytes mode (newEntry mode source) fresh ++
      DwordOwner.bytes mode (directionEntry mode source) direction ++ pointerBytes mode (stateEntry mode source) newState)
    (by simpa [transitionBytes,List.append_assoc] using current)
  have b := ByteWindow.packet memory copied
    (pointerBytes mode source next ++ DwordOwner.bytes mode (currentEntry mode source) rule ++
      DwordOwner.bytes mode (newEntry mode source) fresh ++ DwordOwner.bytes mode (directionEntry mode source) direction)
    (pointerBytes mode (stateEntry mode source) newState) [] (by simpa [transitionBytes,List.append_assoc] using current)
  exact ⟨by simpa only [List.length_nil,Nat.add_zero] using a,
    by simpa only [List.length_append,pointer_length,DwordOwner.length,stateEntry,directionEntry,newEntry,currentEntry,Nat.add_assoc] using b⟩

theorem initial_current (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode = .x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8OwnerSequence.Intact mode (owners mode l v) (state mode l v backing seed).principal.memory := by
  have originalNode := original_node mode l v r reach backing seed
  have originalTransition := original_transition mode l v r reach backing seed
  have sourceNode := node_windows mode l.sourceNode l.sourceNode v.tape v.back v.forward _ originalNode
  have sourceTransition := transition_windows mode l.sourceTransition l.sourceTransition v.next v.newState v.rule v.fresh v.direction _ originalTransition
  have copiedNode := node_windows mode l.sourceNode (nodeParams mode l).destination v.tape v.back v.forward _ (Listing8CopyTrace.copied_node mode l v r backing seed)
  have copiedTransition := transition_windows mode l.sourceTransition (transitionParams mode l).destination v.next v.newState v.rule v.fresh v.direction _ (Listing8CopyTrace.copied_transition mode l v r backing seed)
  have pointer (q source : Nat) (value : Word mode) (member : q ∈ pointerPositions mode l)
      (current : ByteMemory.bytesAt (Listing8CopyTrace.both mode l (initial mode l v backing seed)).principal.memory q (pointerBytes mode source value).length = pointerBytes mode source value) :
      ByteMemory.bytesAt (state mode l v backing seed).principal.memory q (pointerBytes mode source value).length = pointerBytes mode source value := by
    rw [pointer_length,pointer_frame mode l v r reach backing seed q member]
    simpa only [pointer_length] using current
  have scalar := Listing8ModeOffsets.remaining_owners mode (patchLayout mode l) l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState
    (block_capacity mode l r) r.inputAfter reach (source_field_fits mode l r) _ (Listing8CopyTrace.patch_entry mode l v r backing seed) (Listing8CopyTrace.copied_block mode l v r backing seed)
  rw [←Listing8Initializer.principal_effect] at scalar
  intro owner member
  simp only [owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨sourceNode.1,pointer _ _ _ (by simp [pointerPositions]) copiedNode.1⟩
  · exact ⟨sourceNode.2,pointer _ _ _ (by simp [pointerPositions]) copiedNode.2⟩
  · exact ⟨sourceTransition.1,pointer _ _ _ (by simp [pointerPositions]) copiedTransition.1⟩
  · exact scalar.1
  · exact scalar.2.1
  · exact scalar.2.2
  · exact ⟨sourceTransition.2,pointer _ _ _ (by simp [pointerPositions]) copiedTransition.2⟩

end SmcTuring.Appendix.Listing8OwnerImage

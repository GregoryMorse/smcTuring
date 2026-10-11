module
public import SmcTuring.Appendix.Listing8CopyImage

public section
namespace SmcTuring.Appendix.Listing8CopyTrace
open Native Listing8Prototypes Listing8CopyImage

@[expose] def first (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringMacroEffects.finish mode (nodeParams mode l) state
@[expose] def both (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringMacroEffects.finish mode (transitionParams mode l) (first mode l state)
@[expose] def program (mode : Mode) (l : Layout) :=
  StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size ++
    StringProgram.forms mode (transitionParams mode l).start (transitionParams mode l).source (transitionParams mode l).destination (transitionParams mode l).size

theorem first_ready (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringMacroLayout.Ready mode (nodeParams mode l) (initial mode l v backing seed) :=
  ⟨rfl,rfl,r.node.sizeFits,r.node.codeFits,r.node.sourceFits,r.node.destinationFits,r.node.buffers,
    r.node.sourceOutside,r.node.destinationOutside,initial_node_macro mode l v r backing⟩

theorem first_source (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (initial mode l v backing seed).principal.memory (nodeParams mode l).source (nodeParams mode l).size =
      sourceNodeBytes mode l v := by
  have source := initial_source_node mode l v r backing
  simpa only [sourceNodeBytes,node_length,initial,nodeParams] using source

theorem first_effect (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    first mode l (initial mode l v backing seed) =
      { initial mode l v backing seed with principal := { (initial mode l v backing seed).principal with
        pc := Arithmetic.encodeNat mode (secondStart mode l)
        accumulator := StringInit.accumulator mode (nodeParams mode l).destination (initial mode l v backing seed)
        carry := false
        memory := ByteMemory.putBytes (initial mode l v backing seed).principal.memory (nodeParams mode l).destination (sourceNodeBytes mode l v) } } := by
  rw [first,StringMacroEffects.finish_effect mode _ _ (first_ready mode l v r backing seed),first_source mode l v r backing seed]
  rfl

theorem second_macro (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (first mode l (initial mode l v backing seed)).principal.memory
      (transitionParams mode l).start (StringMacroLayout.bytes mode (transitionParams mode l)).length =
      StringMacroLayout.bytes mode (transitionParams mode l) := by
  rw [first_effect mode l v r backing seed,byte_frame]
  · exact initial_transition_macro mode l v r backing
  · right
    have ending := (coordinates mode l).2.1
    change secondStart mode l+(StringMacroLayout.bytes mode (transitionParams mode l)).length ≤ _
    simp only [nodeParams,Listing8ModeOffsets.nodeEntry,patchLayout]
    omega

theorem second_ready (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringMacroLayout.Ready mode (transitionParams mode l) (first mode l (initial mode l v backing seed)) := by
  refine ⟨?_,?_,r.transition.sizeFits,r.transition.codeFits,r.transition.sourceFits,r.transition.destinationFits,
    r.transition.buffers,r.transition.sourceOutside,r.transition.destinationOutside,second_macro mode l v r backing seed⟩
  · rw [first_effect mode l v r backing seed]
    rfl
  · rw [first_effect mode l v r backing seed]
    rfl

theorem second_source (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (first mode l (initial mode l v backing seed)).principal.memory
      (transitionParams mode l).source (transitionParams mode l).size = sourceTransitionBytes mode l v := by
  have d := destinations mode l
  have ending := code_to_input mode l r
  have nlen : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have tlen : (sourceTransitionBytes mode l v).length = transitionSpan mode := transition_length mode _ _ _ _ _ _
  rw [first_effect mode l v r backing seed,byte_frame]
  · simpa only [initial,transitionParams,tlen] using initial_source_transition mode l v backing
  · rw [nlen]
    change (nodeParams mode l).destination+nodeSpan mode ≤ l.sourceTransition ∨
      l.sourceTransition+transitionSpan mode ≤ (nodeParams mode l).destination
    rcases r.transitionOutside with before | after
    · right; omega
    · left; omega

theorem second_effect (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    both mode l (initial mode l v backing seed) =
      { first mode l (initial mode l v backing seed) with
        principal := { (first mode l (initial mode l v backing seed)).principal with
          pc := Arithmetic.encodeNat mode (patchStart mode l)
          accumulator := StringInit.accumulator mode (transitionParams mode l).destination (first mode l (initial mode l v backing seed))
          carry := false
          memory := ByteMemory.putBytes (first mode l (initial mode l v backing seed)).principal.memory
            (transitionParams mode l).destination (sourceTransitionBytes mode l v) } } := by
  rw [both,StringMacroEffects.finish_effect mode _ _ (second_ready mode l v r backing seed),second_source mode l v r backing seed]
  rfl

/-- Both printed TRANSFERDATA calls execute in the same state and memory.
The second Ready is derived from the initial global image and the first exact
effect, rather than supplied by the caller. -/
theorem copies_trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringExecution.Trace mode (initial mode l v backing seed) (program mode l) (both mode l (initial mode l v backing seed)) :=
  StringExecution.trace_append mode
    (StringMacroTrace.trace mode _ _ (first_ready mode l v r backing seed))
    (StringMacroTrace.trace mode _ _ (second_ready mode l v r backing seed))

theorem copied_node (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (both mode l (initial mode l v backing seed)).principal.memory (nodeParams mode l).destination
      (sourceNodeBytes mode l v).length = sourceNodeBytes mode l v := by
  rw [second_effect mode l v r backing seed,byte_frame]
  · rw [first_effect mode l v r backing seed]
    exact ByteMemory.bytes_at_put _ _ _
  · right
    rw [show (sourceNodeBytes mode l v).length = nodeSpan mode from node_length mode _ _ _ _]
    exact (destinations mode l).2.1.le
theorem copied_transition (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (both mode l (initial mode l v backing seed)).principal.memory (transitionParams mode l).destination
      (sourceTransitionBytes mode l v).length = sourceTransitionBytes mode l v := by
  rw [second_effect mode l v r backing seed]
  exact ByteMemory.bytes_at_put _ _ _

theorem retained_patches (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (both mode l (initial mode l v backing seed)).principal.memory (patchStart mode l) (patchBytes mode l).length = patchBytes mode l := by
  have pLength : (patchBytes mode l).length = 40 := by
    rw [patchBytes,DwordRetargetSequence.bytes_length,Listing8ModeOffsets.sites_length]
  have nodeStart : (nodeParams mode l).destination = patchStart mode l+40 := rfl
  have d := destinations mode l
  rw [second_effect mode l v r backing seed,byte_frame _ _ _ _ _ (Or.inr (by rw [pLength]; omega)),
    first_effect mode l v r backing seed,byte_frame _ _ _ _ _ (Or.inr (by rw [pLength]; omega))]
  exact initial_patches mode l v r backing

/-- The actual two copy effects construct the complete source-addressed
retargeting image, including the previously emitted four patch packets. -/
theorem copied_block (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (both mode l (initial mode l v backing seed)).principal.memory (patchStart mode l)
      (Listing8ModeOffsets.bytes mode (patchLayout mode l) l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState).length =
      Listing8ModeOffsets.bytes mode (patchLayout mode l) l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState := by
  have pLength : (patchBytes mode l).length = 40 := by rw [patchBytes,DwordRetargetSequence.bytes_length,Listing8ModeOffsets.sites_length]
  have nLength : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have firstPair := ByteWindow.join _ (patchStart mode l) (patchBytes mode l) (sourceNodeBytes mode l v)
    (retained_patches mode l v r backing seed) (by simpa only [pLength,nodeParams,Listing8ModeOffsets.nodeEntry,patchLayout] using copied_node mode l v r backing seed)
  have complete := ByteWindow.join _ (patchStart mode l) (patchBytes mode l ++ sourceNodeBytes mode l v)
    (sourceTransitionBytes mode l v) firstPair (by
      simpa only [List.length_append,pLength,nLength,transitionParams,Listing8ModeOffsets.transitionEntry,
        Listing8ModeOffsets.nodeEntry,patchLayout,Nat.add_assoc] using copied_transition mode l v r backing seed)
  exact complete

theorem patch_entry (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (both mode l (initial mode l v backing seed)).principal.pc = Arithmetic.encodeNat mode (patchStart mode l) := by
  rw [second_effect mode l v r backing seed]

theorem patches_and_tape_trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedDword.Trace mode (both mode l (initial mode l v backing seed)).principal
      (Listing8ModeOffsets.program mode (patchLayout mode l) ++ [.arithmetic (Listing8ModeOffsets.tapeForm mode (patchLayout mode l) v.tape)])
      (Listing8ModeOffsets.tapeState mode (patchLayout mode l) v.tape (both mode l (initial mode l v backing seed)).principal) :=
  Listing8ModeOffsets.tape_owner_trace mode _ l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState
    (block_capacity mode l r) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)) _
    (patch_entry mode l v r backing seed) (copied_block mode l v r backing seed)

theorem input_retained (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8InputMask.Intact mode l.input 0 force force force force (both mode l (initial mode l v backing seed)).principal.memory := by
  have d := destinations mode l
  have afterInput := r.inputAfter
  have nlen : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have tlen : (sourceTransitionBytes mode l v).length = transitionSpan mode := transition_length mode _ _ _ _ _ _
  change ByteMemory.bytesAt (both mode l (initial mode l v backing seed)).principal.memory l.input.start
    (inputBytes mode l).length = inputBytes mode l
  rw [second_effect mode l v r backing seed,byte_frame _ _ _ _ _ (Or.inl (by rw [tlen]; omega)),
    first_effect mode l v r backing seed,byte_frame _ _ _ _ _ (Or.inl (by rw [nlen]; omega))]
  exact initial_input mode l v r backing

theorem indices (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (both mode l (initial mode l v backing seed)).sourceIndex = seed.sourceIndex ∧
    (both mode l (initial mode l v backing seed)).destinationIndex = seed.destinationIndex ∧
    (both mode l (initial mode l v backing seed)).backwards = false ∧
    (both mode l (initial mode l v backing seed)).principal.stack = seed.principal.stack ∧
    (both mode l (initial mode l v backing seed)).principal.carry = false := by
  rw [second_effect mode l v r backing seed,first_effect mode l v r backing seed]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem cursor_retained (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (both mode l (initial mode l v backing seed)).principal.memory (StringCodec.sourceField mode l.start) =
      Arithmetic.encodeNat mode l.sourceNode := by
  have initialWord := (StringMacroImage.initial_words mode _ _ (first_ready mode l v r backing seed)).1
  have nextMacro := endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l ≤ patchStart mode l at nextMacro
  have firstFieldEnd : StringCodec.sourceField mode l.start+mode.wordBytes ≤ secondStart mode l := by
    have field := StringCodec.field_end mode l.start
    have header : StringCodec.endpoint mode l.start (nodeSpan mode) ≥ StringCodec.bodyStart mode l.start := by
      unfold StringCodec.endpoint StringCodec.bodyEnd
      omega
    unfold secondStart StringCodec.bodyStart at *
    omega
  unfold MixedMemory.getWord
  rw [second_effect mode l v r backing seed,byte_frame _ _ _ _ _ (Or.inr (by
    have d := destinations mode l
    have nodeStart : (nodeParams mode l).destination = patchStart mode l+40 := rfl
    omega)),first_effect mode l v r backing seed,byte_frame _ _ _ _ _ (Or.inr (by
    have nodeStart : (nodeParams mode l).destination = patchStart mode l+40 := rfl
    omega))]
  exact initialWord

theorem source_node_retained (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (both mode l (initial mode l v backing seed)).principal.memory l.sourceNode (sourceNodeBytes mode l v).length =
      sourceNodeBytes mode l v := by
  have d := destinations mode l
  have ending := code_to_input mode l r
  have nlen : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have tlen : (sourceTransitionBytes mode l v).length = transitionSpan mode := transition_length mode _ _ _ _ _ _
  have nodeOutside : (nodeParams mode l).destination+(sourceNodeBytes mode l v).length ≤ l.sourceNode ∨
      l.sourceNode+(sourceNodeBytes mode l v).length ≤ (nodeParams mode l).destination := by
    rw [nlen]
    rcases r.nodeOutside with before | after
    · right; omega
    · left; omega
  have transitionOutside : (transitionParams mode l).destination+(sourceTransitionBytes mode l v).length ≤ l.sourceNode ∨
      l.sourceNode+(sourceNodeBytes mode l v).length ≤ (transitionParams mode l).destination := by
    rw [nlen,tlen]
    rcases r.nodeOutside with before | after
    · right; omega
    · left; omega
  rw [second_effect mode l v r backing seed,byte_frame _ _ _ _ _ transitionOutside,
    first_effect mode l v r backing seed,byte_frame _ _ _ _ _ nodeOutside]
  exact initial_source_node mode l v r backing

theorem tape_source_value (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (both mode l (initial mode l v backing seed)).principal.memory (l.sourceNode+6) = v.tape :=
  (node_values mode l.sourceNode v.tape v.back v.forward _ (source_node_retained mode l v r backing seed)).1

end SmcTuring.Appendix.Listing8CopyTrace

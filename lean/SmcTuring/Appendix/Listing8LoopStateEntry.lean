module
public import SmcTuring.Appendix.Listing8LoopState
public import SmcTuring.Appendix.Listing8StateFields
public import SmcTuring.Appendix.Listing8LoopPointerValues

public section
namespace SmcTuring.Appendix.Listing8LoopStateEntry
open Native Listing8CopyImage Listing8StateGeometry Listing8StateFields
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopState.Bounds
abbrev Current:=Listing8LoopState.Current

theorem new_frame (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (observed : Nat) (member : observed∈newFields mode (Listing8StateGeometry.region mode l)) :
    DwordCode.get (Listing8LoopHead.finish mode l t v state).principal.memory observed=
      DwordCode.get (Listing8MainPrefix.finish mode l t v state).principal.memory observed := by
  have spans:=field_span mode (Listing8StateGeometry.region mode l) observed (List.mem_append_left _ member)
  have headFrame:=Listing8LoopStatePrefix.head_window mode l t v old b state entry forward current observed 4 spans.1
  have inputFrame:=Listing8MainInputFrames.input_window mode l t v old b.head.input state entry forward current.head.input observed 4
    (new_input_outside mode l t b.state observed member)
  exact congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) (headFrame.trans inputFrame)

theorem new_low (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    DwordCode.get (Listing8LoopHead.finish mode l t v state).principal.memory (Listing8StateLayout.newPC mode (Listing8StateGeometry.region mode l)+6)=Listing8DirectionFields.low mode v.newState := by
  rw [new_frame mode l t v old b state entry forward current _ (by cases mode <;> simp [newFields]),←b.state.state,
    Listing8LoopPointerValues.memory_effect mode l t v b.head.input.input.prefixBounds state entry forward current.head.input.prefixCurrent,
    Listing8DirectionFields.pointer_frame mode _ t.forward v.forward (t.state+6)
      (Or.inl (Listing8StateEntryValues.neighbor_before mode l t b.state t.forward (by simp))),
    Listing8DirectionFields.pointer_frame mode _ t.back v.back (t.state+6)
      (Or.inl (Listing8StateEntryValues.neighbor_before mode l t b.state t.back (by simp))),Listing8DirectionFields.pointer_low]

theorem new_high (l : Layout) (t : Targets) (v : Values .x64) (old : OldInput) (b : Bounds .x64 l t v)
    (state : StringExecution.State .x64) (entry : state.principal.pc=Arithmetic.encodeNat .x64 l.start)
    (forward : state.backwards=false) (current : Current .x64 l t v old state.principal.memory) :
    DwordCode.get (Listing8LoopHead.finish .x64 l t v state).principal.memory (Listing8StateLayout.newPC .x64 (Listing8StateGeometry.region .x64 l)+16)=X64.HalfWords.high v.newState := by
  have fwdBefore:=Listing8StateEntryValues.neighbor_before .x64 l t b.state t.forward (by simp)
  have backBefore:=Listing8StateEntryValues.neighbor_before .x64 l t b.state t.back (by simp)
  simp only [reduceCtorEq,ite_false] at fwdBefore backBefore
  rw [new_frame .x64 l t v old b state entry forward current _ (by simp [newFields]),←b.state.state,
    Listing8LoopPointerValues.memory_effect .x64 l t v b.head.input.input.prefixBounds state entry forward current.head.input.prefixCurrent,
    Listing8DirectionFields.pointer_frame .x64 _ t.forward v.forward (t.state+16) (Or.inl (by simp only [reduceCtorEq,ite_false];omega)),
    Listing8DirectionFields.pointer_frame .x64 _ t.back v.back (t.state+16) (Or.inl (by simp only [reduceCtorEq,ite_false];omega)),Listing8DirectionFields.pointer_high]

theorem mask (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (observed : Nat) (field : observed∈maskFields mode (Listing8StateGeometry.region mode l)) :
    DwordCode.get (Listing8LoopHead.finish mode l t v state).principal.memory observed=InputUpdate.mask (Listing8LiteralInput.chosen v.rule v.tape) := by
  have spans:=field_span mode (Listing8StateGeometry.region mode l) observed (List.mem_append_right _ field)
  have frame:=Listing8LoopStatePrefix.head_window mode l t v old b state entry forward current observed 4 spans.1
  have kept:=congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) frame
  change DwordCode.get (Listing8LoopHead.finish mode l t v state).principal.memory observed=
    DwordCode.get (Listing8MainInput.finish mode l t v state).principal.memory observed at kept
  rw [kept]
  have placed : observed∈(Listing8LiteralInput.distributionLayouts mode l.input).map (fun helper => helper.destination) := by
    simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts]
    rw [b.state.mask]
    cases mode
    all_goals simp only [maskFields,List.mem_cons,List.not_mem_nil,or_false] at field
    all_goals rcases field with rfl | rfl
    all_goals simp
  rcases List.mem_map.mp placed with ⟨reader,member,hit⟩
  rw [←hit]
  have preBounds:=b.head.input.input.prefixBounds
  exact Listing8InputMaskEffects.destination_values mode l.input v.rule v.tape old.pending v.fresh old.mask
    preBounds.resources.inputFits (Listing8InputBounds.masks mode l preBounds.fields)
    (Listing8HeadGeometry.masks_separate mode l t b.state.head)
    (Listing8InputBounds.update mode l t preBounds.fields preBounds.joined preBounds.resources)
    (Listing8InputBounds.outside mode l t preBounds.fields preBounds.joined preBounds.resources) _
    (Listing8MainPrefix.entry mode l t v preBounds state entry forward current.head.input.prefixCurrent)
    (Listing8MainInputImage.current mode l t v old b.head.input.input state entry forward current.head.input)
    (Listing8MainPrefixFrames.head_cursor mode l t v preBounds state entry forward current.head.input.prefixCurrent)
    (Listing8MainPrefixSources.tape_symbol mode l t v preBounds b.head.input.pointersOutside state entry forward current.head.input.prefixCurrent) reader member

theorem cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    MixedMemory.getWord mode (Listing8LoopHead.finish mode l t v state).principal.memory (Listing8StateGeometry.region mode l).cursor=v.next := by
  have tail:=Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t b.state.head) (Listing8LoopDirection.finish mode l t v state)
    (Listing8LoopDirection.endpoint mode l t v old b.head state entry forward current.head) (Listing8StateGeometry.region mode l).cursor mode.wordBytes
    (cursor_tail_xors mode l t b.head.input.input.prefixBounds.resources b.state)
    (fun writer member => cursor_tail_packets mode l t b.head.input.input.prefixBounds.resources b.state writer (List.mem_append_left _ member))
    (fun writer member => cursor_tail_packets mode l t b.head.input.input.prefixBounds.resources b.state writer (List.mem_append_right _ member))
  have direction:=Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) b.state.head.capacity
    (Listing8MainInput.finish mode l t v state) (Listing8MainInput.endpoint mode l t v old b.head.input state entry forward current.head.input) (Listing8StateGeometry.region mode l).cursor mode.wordBytes
    (cursor_selection_helpers mode l t b.head.input.input.prefixBounds.resources b.state) (cursor_selection_packets mode l t b.head.input.input.prefixBounds.resources b.state)
  have inputFrame:=Listing8MainInputFrames.input_window mode l t v old b.head.input state entry forward current.head.input
    (Listing8StateGeometry.region mode l).cursor mode.wordBytes
    (cursor_input_outside mode l t b.head.input.input.prefixBounds.resources b.state)
  have kept:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes)) ((tail.trans direction).trans inputFrame)
  change MixedMemory.getWord mode (Listing8LoopHead.finish mode l t v state).principal.memory (Listing8StateGeometry.region mode l).cursor=
    MixedMemory.getWord mode (Listing8MainPrefix.finish mode l t v state).principal.memory (Listing8StateGeometry.region mode l).cursor at kept
  rw [kept]
  exact Listing8LoopPointerValues.transition_cursor mode l t v b.head.input.input.prefixBounds state entry forward current.head.input.prefixCurrent

end SmcTuring.Appendix.Listing8LoopStateEntry

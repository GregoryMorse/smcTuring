module
public import SmcTuring.Appendix.Listing8StateFields

public section
namespace SmcTuring.Appendix.Listing8StateEntryValues
open Native Listing8CopyImage Listing8StateGeometry Listing8StateFields
abbrev Targets := Listing8PointerCopies.Targets

theorem new_frame (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed : Nat) (member : observed ∈ newFields mode (region mode l)) :
    DwordCode.get (Listing8GlobalState.entryState mode l t v extra seed).principal.memory observed =
      DwordCode.get (Listing8PointerImage.finish mode l t v
        (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l extra)) seed).principal.memory observed := by
  have spans := field_span mode (region mode l) observed (List.mem_append_left _ member)
  have headFrame := Listing8StateFrames.after_head mode l t v r owners copies bounds (Listing8StateImage.backing mode l extra) seed observed 4 spans.1
  have inputFrame := Listing8GlobalWindows.input mode l t v r owners copies bounds.head.input
    (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l extra)) seed observed 4
    (new_input_outside mode l t bounds observed member)
  exact congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) (headFrame.trans inputFrame)

theorem neighbor_before (mode : Mode) (l : Layout) (t : Targets) (bounds : Bounds mode l t) (pc : Nat)
    (member : pc ∈ [t.back,t.forward]) : pc+(if mode = .x86 then 10 else 20) ≤ t.state+6 := by
  rw [bounds.state]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals first | rw [bounds.head.back] | rw [bounds.head.forward]
  all_goals cases mode <;> simp [region,Listing8StateLayout.newPC,Listing8StateLayout.halves,
    Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
    Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
    Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem new_low (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GlobalState.entryState mode l t v extra seed).principal.memory
      (Listing8StateLayout.newPC mode (region mode l)+6) = Listing8DirectionFields.low mode v.newState := by
  rw [new_frame mode l t v r owners copies bounds extra seed _ (by cases mode <;> simp [newFields]),←bounds.state,
    Listing8PointerValues.memory_effect mode l t v r owners copies _ seed,
    Listing8DirectionFields.pointer_frame mode _ t.forward v.forward (t.state+6)
      (Or.inl (neighbor_before mode l t bounds t.forward (by simp))),
    Listing8DirectionFields.pointer_frame mode _ t.back v.back (t.state+6)
      (Or.inl (neighbor_before mode l t bounds t.back (by simp))),Listing8DirectionFields.pointer_low]

theorem new_high (l : Layout) (t : Targets) (v : Values .x64) (r : Resources .x64 l)
    (owners : Listing8CopiedOwners.Bounds .x64 l v) (copies : Listing8PointerCopies.Bounds .x64 l t)
    (bounds : Bounds .x64 l t) (extra : ByteMemory.Memory) (seed : StringExecution.State .x64) :
    DwordCode.get (Listing8GlobalState.entryState .x64 l t v extra seed).principal.memory
      (Listing8StateLayout.newPC .x64 (region .x64 l)+16) = X64.HalfWords.high v.newState := by
  have forward := neighbor_before .x64 l t bounds t.forward (by simp)
  have back := neighbor_before .x64 l t bounds t.back (by simp)
  simp only [reduceCtorEq,ite_false] at forward back
  rw [new_frame .x64 l t v r owners copies bounds extra seed _ (by simp [newFields]),←bounds.state,
    Listing8PointerValues.memory_effect .x64 l t v r owners copies _ seed,
    Listing8DirectionFields.pointer_frame .x64 _ t.forward v.forward (t.state+16) (Or.inl (by simp only [reduceCtorEq,ite_false];omega)),
    Listing8DirectionFields.pointer_frame .x64 _ t.back v.back (t.state+16) (Or.inl (by simp only [reduceCtorEq,ite_false];omega)),Listing8DirectionFields.pointer_high]

theorem mask (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed : Nat) (field : observed ∈ maskFields mode (region mode l)) :
    DwordCode.get (Listing8GlobalState.entryState mode l t v extra seed).principal.memory observed =
      InputUpdate.mask (Listing8LiteralInput.chosen v.rule v.tape) := by
  have spans := field_span mode (region mode l) observed (List.mem_append_right _ field)
  have frame := Listing8StateFrames.after_head mode l t v r owners copies bounds (Listing8StateImage.backing mode l extra) seed observed 4 spans.1
  have value := congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) frame
  change DwordCode.get (Listing8GlobalState.entryState mode l t v extra seed).principal.memory observed =
    DwordCode.get (Listing8GlobalDirection.entryState mode l t v (Listing8StateImage.backing mode l extra) seed).principal.memory observed at value
  rw [value]
  have placed : observed ∈ (Listing8LiteralInput.distributionLayouts mode l.input).map (fun helper => helper.destination) := by
    simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts]
    rw [bounds.mask]
    cases mode
    all_goals simp only [maskFields,List.mem_cons,List.not_mem_nil,or_false] at field
    all_goals rcases field with rfl | rfl
    all_goals simp
  rcases List.mem_map.mp placed with ⟨reader,member,hit⟩
  rw [←hit]
  exact Listing8InputMaskEffects.destination_values mode l.input v.rule v.tape Listing8DirectionLayout.force v.fresh Listing8DirectionLayout.force
    r.inputFits (Listing8InputBounds.masks mode l bounds.head.input.fields) (Listing8HeadGeometry.masks_separate mode l t bounds.head)
    (Listing8InputBounds.update mode l t bounds.head.input.fields bounds.head.input.joined r)
    (Listing8InputBounds.outside mode l t bounds.head.input.fields bounds.head.input.joined r)
    (Listing8GlobalInput.entryState mode l t v (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l extra)) seed).principal
    (Listing8GlobalInput.entry mode l t v r owners copies bounds.head.input _ seed)
    (Listing8GlobalInput.input_image mode l t v r owners copies bounds.head.input _ seed)
    (Listing8GlobalInput.cursor mode l t v r owners copies bounds.head.input _ seed)
    (Listing8GlobalInput.symbol mode l t v r owners copies bounds.head.input _ seed) reader member

theorem cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GlobalState.entryState mode l t v extra seed).principal.memory (region mode l).cursor = v.next := by
  let memory := Listing8StateImage.backing mode l extra
  have tail := Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t bounds.head) (Listing8GlobalHead.entryState mode l t v memory seed)
    (Listing8GlobalHead.entry mode l t v r owners copies bounds.head memory seed) (region mode l).cursor mode.wordBytes
    (cursor_tail_xors mode l t r bounds)
    (fun writer member => cursor_tail_packets mode l t r bounds writer (List.mem_append_left _ member))
    (fun writer member => cursor_tail_packets mode l t r bounds writer (List.mem_append_right _ member))
  have selection := Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) bounds.head.capacity
    (Listing8GlobalDirection.entryState mode l t v memory seed) (Listing8GlobalDirection.entry mode l t v r owners copies bounds.head memory seed)
    (region mode l).cursor mode.wordBytes (cursor_selection_helpers mode l t r bounds) (cursor_selection_packets mode l t r bounds)
  have input := Listing8GlobalWindows.input mode l t v r owners copies bounds.head.input
    (Listing8DirectionImage.backing mode l memory) seed (region mode l).cursor mode.wordBytes (cursor_input_outside mode l t r bounds)
  have preserved := congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes)) ((tail.trans selection).trans input)
  change MixedMemory.getWord mode (Listing8GlobalState.entryState mode l t v extra seed).principal.memory (region mode l).cursor =
    MixedMemory.getWord mode (Listing8PointerImage.finish mode l t v (Listing8DirectionImage.backing mode l memory) seed).principal.memory (region mode l).cursor at preserved
  rw [preserved]
  exact Listing8PointerValues.transition_cursor mode l t v r owners copies (Listing8DirectionImage.backing mode l memory) seed

end SmcTuring.Appendix.Listing8StateEntryValues

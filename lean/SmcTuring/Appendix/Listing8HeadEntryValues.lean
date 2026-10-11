module
public import SmcTuring.Appendix.Listing8HeadGeometry

public section
namespace SmcTuring.Appendix.Listing8HeadEntryValues
open Native Listing8CopyImage Listing8DirectionGeometry Listing8HeadGeometry
abbrev Targets := Listing8PointerCopies.Targets

theorem input_mask (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed : Nat) (field : observed ∈ maskFields mode (region mode l)) :
    DwordCode.get (Listing8GlobalInput.finish mode l t v (Listing8DirectionImage.backing mode l extra) seed).principal.memory observed =
      InputUpdate.mask (Listing8LiteralInput.chosen v.rule v.tape) := by
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
    r.inputFits (Listing8InputBounds.masks mode l bounds.input.fields) (masks_separate mode l t bounds)
    (Listing8InputBounds.update mode l t bounds.input.fields bounds.input.joined r)
    (Listing8InputBounds.outside mode l t bounds.input.fields bounds.input.joined r)
    (Listing8GlobalInput.entryState mode l t v (Listing8DirectionImage.backing mode l extra) seed).principal
    (Listing8GlobalInput.entry mode l t v r owners copies bounds.input _ seed)
    (Listing8GlobalInput.input_image mode l t v r owners copies bounds.input _ seed)
    (Listing8GlobalInput.cursor mode l t v r owners copies bounds.input _ seed)
    (Listing8GlobalInput.symbol mode l t v r owners copies bounds.input _ seed) reader member

theorem mask (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed : Nat) (field : observed ∈ maskFields mode (region mode l)) :
    DwordCode.get (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory observed =
      InputUpdate.mask (Listing8LiteralInput.chosen v.rule v.tape) := by
  have frame := Listing8DirectionTrace.window mode (region mode l) bounds.capacity
    (Listing8GlobalDirection.entryState mode l t v extra seed) (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed)
    observed 4 (mask_helpers mode (region mode l) observed field) (mask_packets mode (region mode l) observed field)
  have value := congrArg (fun data => BitVec.ofNat 32 (LittleEndian.pack data)) frame
  change DwordCode.get (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory observed =
    DwordCode.get (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory observed at value
  rw [value]
  exact input_mask mode l t v r owners copies bounds extra seed observed field

theorem cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory l.input.cursor =
      Arithmetic.encodeNat mode l.sourceNode := by
  have selection := Listing8DirectionTrace.window mode (region mode l) bounds.capacity
    (Listing8GlobalDirection.entryState mode l t v extra seed) (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed)
    l.input.cursor mode.wordBytes (cursor_helpers mode (region mode l) (tail_bounds mode l t bounds))
    (cursor_packets mode (region mode l) (tail_bounds mode l t bounds))
  have input := Listing8GlobalWindows.input mode l t v r owners copies bounds.input (Listing8DirectionImage.backing mode l extra) seed
    l.input.cursor mode.wordBytes (cursor_input_outside mode l t r bounds)
  have kept := congrArg (fun data => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack data)) selection
  have prior := congrArg (fun data => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack data)) input
  change MixedMemory.getWord mode (Listing8GlobalDirection.finish mode l t v extra seed).principal.memory l.input.cursor =
    MixedMemory.getWord mode (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory l.input.cursor at kept
  rw [kept,show MixedMemory.getWord mode (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory l.input.cursor = _ from prior]
  have initial := Listing8GlobalInput.cursor mode l t v r owners copies bounds.input (Listing8DirectionImage.backing mode l extra) seed
  simpa only [bounds.input.fields.headLabel,MixedMemory.getWord] using initial

end SmcTuring.Appendix.Listing8HeadEntryValues

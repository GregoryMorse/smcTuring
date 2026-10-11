module
public import SmcTuring.Appendix.Listing8GlobalHead
public import SmcTuring.Appendix.Listing8HeadEntryValues
public import SmcTuring.Appendix.Listing8HeadTailMemory

public section
namespace SmcTuring.Appendix.Listing8HeadValues
open Native Listing8CopyImage Listing8DirectionGeometry
abbrev Targets := Listing8PointerCopies.Targets

/-- The full actual initialized prefix moves the head to the selected
neighbor iff rule/tape match; rejection retains the original source head. -/
theorem head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (takeBack : Bool) (encoded : v.direction = if takeBack then BitVec.allOnes 32 else 0) :
    MixedMemory.getWord mode (Listing8GlobalHead.finish mode l t v extra seed).principal.memory l.input.cursor =
      if Listing8LiteralInput.chosen v.rule v.tape then (if takeBack then v.back else v.forward)
      else Arithmetic.encodeNat mode l.sourceNode := by
  have selected := Listing8DirectionSelected.selected mode l t v r owners copies bounds extra seed takeBack encoded
  have cursor := Listing8HeadEntryValues.cursor mode l t v r owners copies bounds extra seed
  have mask := Listing8HeadEntryValues.mask mode l t v r owners copies bounds extra seed
    (Listing8DirectionLayout.maskPC mode (region mode l)+6) (by cases mode <;> simp [Listing8HeadGeometry.maskFields])
  have tail := Listing8HeadGeometry.tail_bounds mode l t bounds
  have entry := Listing8GlobalHead.entry mode l t v r owners copies bounds extra seed
  cases mode with
  | x86 =>
    let neighbor : BitVec 32 := if takeBack then v.back else v.forward
    let original : BitVec 32 := Arithmetic.encodeNat .x86 l.sourceNode
    change DwordCode.get (Listing8HeadTailTrace.finish .x86 (region .x86 l)
      (Listing8GlobalHead.entryState .x86 l t v extra seed)).principal.memory (region .x86 l).cursor =
        if Listing8LiteralInput.chosen v.rule v.tape then neighbor else original
    rw [Listing8HeadTailMemory.low_cursor .x86 (region .x86 l) tail _ entry]
    have selectedValue : DwordCode.get (Listing8GlobalDirection.finish .x86 l t v extra seed).principal.memory
      (Listing8DirectionLayout.directionPC .x86 (region .x86 l)+6) = neighbor := selected
    have cursorValue : DwordCode.get (Listing8GlobalDirection.finish .x86 l t v extra seed).principal.memory l.input.cursor = original := cursor
    simp only [Listing8GlobalHead.entryState,region] at selectedValue cursorValue mask ⊢
    rw [selectedValue,cursorValue,mask,Listing8HeadTailMemory.selected]
  | x64 =>
    let neighbor : BitVec 64 := if takeBack then v.back else v.forward
    let original : BitVec 64 := Arithmetic.encodeNat .x64 l.sourceNode
    have selectedValue : Listing8DirectionSelected.value .x64
      (Listing8GlobalDirection.finish .x64 l t v extra seed).principal.memory
      (Listing8DirectionLayout.directionPC .x64 (region .x64 l)) = neighbor := selected
    have cursorValue : MixedMemory.getWord .x64
      (Listing8GlobalDirection.finish .x64 l t v extra seed).principal.memory l.input.cursor = original := cursor
    have highMask := Listing8HeadEntryValues.mask .x64 l t v r owners copies bounds extra seed
      (Listing8DirectionLayout.maskPC .x64 (region .x64 l)+16) (by simp [Listing8HeadGeometry.maskFields])
    have lowSelected := congrArg X64.HalfWords.low selectedValue
    have highSelected := congrArg X64.HalfWords.high selectedValue
    simp only [Listing8DirectionSelected.value,X64.HalfWords.low_pack] at lowSelected
    simp only [Listing8DirectionSelected.value,X64.HalfWords.high_pack] at highSelected
    have lowCursor := (PointerHalves.low_get (Listing8GlobalDirection.finish .x64 l t v extra seed).principal.memory l.input.cursor).trans
      (congrArg X64.HalfWords.low cursorValue)
    have highCursor := (PointerHalves.high_get (Listing8GlobalDirection.finish .x64 l t v extra seed).principal.memory l.input.cursor).trans
      (congrArg X64.HalfWords.high cursorValue)
    rw [PointerHalves.split_get]
    change X64.HalfWords.pack
      (DwordCode.get (Listing8HeadTailTrace.finish .x64 (region .x64 l) (Listing8GlobalHead.entryState .x64 l t v extra seed)).principal.memory (region .x64 l).cursor)
      (DwordCode.get (Listing8HeadTailTrace.finish .x64 (region .x64 l) (Listing8GlobalHead.entryState .x64 l t v extra seed)).principal.memory ((region .x64 l).cursor+4)) =
        if Listing8LiteralInput.chosen v.rule v.tape then neighbor else original
    rw [Listing8HeadTailMemory.low_cursor .x64 (region .x64 l) tail _ entry,
      Listing8HeadTailMemory.high_cursor (region .x64 l) tail _ entry]
    simp only [Listing8GlobalHead.entryState,region] at lowSelected highSelected lowCursor highCursor mask highMask ⊢
    rw [lowSelected,highSelected,lowCursor,highCursor,mask,highMask,
      Listing8HeadTailMemory.selected,Listing8HeadTailMemory.selected]
    cases Listing8LiteralInput.chosen v.rule v.tape <;> exact X64.HalfWords.pack_halves _

theorem tape (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GlobalHead.finish mode l t v extra seed).principal.memory (l.sourceNode+6) =
      if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape := by
  have input := Listing8InputBounds.positions mode l t bounds.input.fields bounds.input.joined
  have selectionOutside (field : Nat) (location : l.start ≤ field ∧ field+4 ≤ Listing8DirectionLayout.endPC mode (region mode l)) :=
    Listing8HeadGeometry.source_field_outside mode l t bounds field location
  have helperFields : ∀ writer ∈ Listing8DirectionLayout.helpers mode (region mode l),
      writer.destination+4 ≤ l.sourceNode+6 ∨ l.sourceNode+10 ≤ writer.destination := by
    intro writer member
    apply selectionOutside
    cases mode
    all_goals simp only [Listing8DirectionLayout.helpers,Listing8DirectionLayout.duplicate,Listing8DirectionLayout.copy,
      List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl
    all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
      Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
      Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
      Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
      DwordLayout.span,DwordLayout.storeSize,region] at input ⊢ <;> omega
  have packetFields : ∀ writer ∈ Listing8DirectionLayout.arithmetic mode (region mode l),
      writer.target+4 ≤ l.sourceNode+6 ∨ l.sourceNode+10 ≤ writer.target := by
    intro writer member
    apply selectionOutside
    cases mode
    all_goals simp only [Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.group,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
      Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
      Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
      Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
      DwordLayout.span,DwordLayout.storeSize,region] at input ⊢ <;> omega
  have xorFields : ∀ writer ∈ Listing8HeadTailBounds.xorLayouts mode (region mode l),
      writer.destination+4 ≤ l.sourceNode+6 ∨ l.sourceNode+10 ≤ writer.destination := by
    intro writer member
    apply selectionOutside
    cases mode
    all_goals simp only [Listing8HeadTailBounds.xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl
    all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
      Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
      Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
      Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
      DwordLayout.span,DwordLayout.storeSize,region] at input ⊢ <;> omega
  have tailFields : ∀ writer ∈ Listing8DirectionLayout.masks mode (region mode l) ++ Listing8DirectionLayout.heads mode (region mode l),
      writer.target+4 ≤ l.sourceNode+6 ∨ l.sourceNode+10 ≤ writer.target := by
    intro writer member
    apply selectionOutside
    cases mode
    all_goals simp only [Listing8DirectionLayout.masks,Listing8DirectionLayout.heads,Listing8DirectionLayout.group,
      List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl
    all_goals simp [Listing8DirectionLayout.endPC,Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,
      Listing8DirectionLayout.selectionEnd,Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,
      Listing8DirectionLayout.notPC,Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,
      Listing8DirectionLayout.duplicateSpan,Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,
      DwordLayout.span,DwordLayout.storeSize,region] at input ⊢ <;> omega
  have tailFrame := Listing8HeadTailTrace.window mode (region mode l) (Listing8HeadGeometry.tail_bounds mode l t bounds)
    (Listing8GlobalHead.entryState mode l t v extra seed) (Listing8GlobalHead.entry mode l t v r owners copies bounds extra seed)
    (l.sourceNode+6) 4 xorFields
    (fun writer member => tailFields writer (List.mem_append_left _ member))
    (fun writer member => tailFields writer (List.mem_append_right _ member))
  have selectionFrame := Listing8DirectionTrace.window mode (region mode l) bounds.capacity
    (Listing8GlobalDirection.entryState mode l t v extra seed) (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed)
    (l.sourceNode+6) 4 helperFields packetFields
  have allFrames := congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) (tailFrame.trans selectionFrame)
  change DwordCode.get (Listing8GlobalHead.finish mode l t v extra seed).principal.memory (l.sourceNode+6) =
    DwordCode.get (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory (l.sourceNode+6) at allFrames
  rw [allFrames]
  have result := Listing8GlobalInput.tape_value mode l t v r owners copies bounds.input (Listing8DirectionImage.backing mode l extra) seed
  simpa only [bounds.input.fields.headLabel,Listing8GlobalDirection.entryState] using result

end SmcTuring.Appendix.Listing8HeadValues

module
public import SmcTuring.Appendix.Listing8StateEntryValues
public import SmcTuring.Appendix.Listing8StateMemory
public import SmcTuring.Appendix.Listing8HeadValues

public section
namespace SmcTuring.Appendix.Listing8StateValues
open Native Listing8CopyImage Listing8StateGeometry
abbrev Targets := Listing8PointerCopies.Targets

/-- All transition-pointer operands are derived from initialization and
actual earlier effects. Matching selects the new state; rejection follows next. -/
theorem transition (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GlobalState.finish mode l t v extra seed).principal.memory (region mode l).cursor =
      if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next := by
  have cursor := Listing8StateEntryValues.cursor mode l t v r owners copies bounds extra seed
  have fresh := Listing8StateEntryValues.new_low mode l t v r owners copies bounds extra seed
  have mask := Listing8StateEntryValues.mask mode l t v r owners copies bounds extra seed
    (Listing8StateLayout.maskPC mode (region mode l)+6) (by cases mode <;> simp [Listing8StateFields.maskFields])
  have valid := local_bounds mode l t r bounds
  have entry := Listing8GlobalState.entry mode l t v r owners copies bounds extra seed
  cases mode with
  | x86 =>
    let old : BitVec 32 := v.next
    let new : BitVec 32 := v.newState
    have cursorValue : DwordCode.get (Listing8GlobalState.entryState .x86 l t v extra seed).principal.memory (region .x86 l).cursor = old := cursor
    have newValue : DwordCode.get (Listing8GlobalState.entryState .x86 l t v extra seed).principal.memory
      (Listing8StateLayout.newPC .x86 (region .x86 l)+6) = new := fresh
    change DwordCode.get (Listing8StateTrace.finish .x86 (region .x86 l) (Listing8GlobalState.entryState .x86 l t v extra seed)).principal.memory
      (region .x86 l).cursor = if Listing8LiteralInput.chosen v.rule v.tape then new else old
    rw [Listing8StateMemory.low_cursor .x86 (region .x86 l) valid _ entry,cursorValue,newValue,mask,Listing8StateMemory.selected]
  | x64 =>
    let old : BitVec 64 := v.next
    let new : BitVec 64 := v.newState
    have cursorValue : MixedMemory.getWord .x64 (Listing8GlobalState.entryState .x64 l t v extra seed).principal.memory (region .x64 l).cursor = old := cursor
    have lowNew : DwordCode.get (Listing8GlobalState.entryState .x64 l t v extra seed).principal.memory
      (Listing8StateLayout.newPC .x64 (region .x64 l)+6) = X64.HalfWords.low new := fresh
    have highNew := Listing8StateEntryValues.new_high l t v r owners copies bounds extra seed
    have highMask := Listing8StateEntryValues.mask .x64 l t v r owners copies bounds extra seed
      (Listing8StateLayout.maskPC .x64 (region .x64 l)+16) (by simp [Listing8StateFields.maskFields])
    have lowOld := (PointerHalves.low_get (Listing8GlobalState.entryState .x64 l t v extra seed).principal.memory (region .x64 l).cursor).trans
      (congrArg X64.HalfWords.low cursorValue)
    have highOld := (PointerHalves.high_get (Listing8GlobalState.entryState .x64 l t v extra seed).principal.memory (region .x64 l).cursor).trans
      (congrArg X64.HalfWords.high cursorValue)
    rw [PointerHalves.split_get]
    change X64.HalfWords.pack
      (DwordCode.get (Listing8StateTrace.finish .x64 (region .x64 l) (Listing8GlobalState.entryState .x64 l t v extra seed)).principal.memory (region .x64 l).cursor)
      (DwordCode.get (Listing8StateTrace.finish .x64 (region .x64 l) (Listing8GlobalState.entryState .x64 l t v extra seed)).principal.memory ((region .x64 l).cursor+4)) =
        if Listing8LiteralInput.chosen v.rule v.tape then new else old
    rw [Listing8StateMemory.low_cursor .x64 (region .x64 l) valid _ entry,
      Listing8StateMemory.high_cursor (region .x64 l) valid _ entry,lowOld,highOld,lowNew,highNew,mask,highMask,
      Listing8StateMemory.selected,Listing8StateMemory.selected]
    cases Listing8LiteralInput.chosen v.rule v.tape <;> exact X64.HalfWords.pack_halves _

theorem head_frame (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GlobalState.finish mode l t v extra seed).principal.memory l.input.cursor =
      MixedMemory.getWord mode (Listing8GlobalState.entryState mode l t v extra seed).principal.memory l.input.cursor := by
  have before := (local_bounds mode l t r bounds).cursorBefore
  have first := Listing8StateFields.first_cursor_before mode l t bounds
  have helpers : ∀ writer ∈ Listing8StateLayout.helpers mode (region mode l),
      writer.destination+4 ≤ l.input.cursor ∨ l.input.cursor+mode.wordBytes ≤ writer.destination := by
    intro writer member
    right
    cases mode
    all_goals simp only [Listing8StateLayout.helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl
    all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
      Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at before first ⊢ <;> omega
  have packets : ∀ writer ∈ Listing8StateLayout.packets mode (region mode l),
      writer.target+4 ≤ l.input.cursor ∨ l.input.cursor+mode.wordBytes ≤ writer.target := by
    intro writer member
    right
    cases mode
    all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
      Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
      Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at before first ⊢ <;> omega
  exact congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes))
    (Listing8StateTrace.window mode (region mode l) (local_bounds mode l t r bounds) _
      (Listing8GlobalState.entry mode l t v r owners copies bounds extra seed) l.input.cursor mode.wordBytes helpers packets)

theorem head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (takeBack : Bool) (encoded : v.direction = if takeBack then BitVec.allOnes 32 else 0) :
    MixedMemory.getWord mode (Listing8GlobalState.finish mode l t v extra seed).principal.memory l.input.cursor =
      if Listing8LiteralInput.chosen v.rule v.tape then (if takeBack then v.back else v.forward)
      else Arithmetic.encodeNat mode l.sourceNode := by
  rw [head_frame mode l t v r owners copies bounds extra seed]
  exact Listing8HeadValues.head mode l t v r owners copies bounds.head (Listing8StateImage.backing mode l extra) seed takeBack encoded

theorem tape (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GlobalState.finish mode l t v extra seed).principal.memory (l.sourceNode+6) =
      if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape := by
  have coords := positions mode l t bounds
  have large : 10 ≤ Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  have outside (field : Nat) (span : l.start ≤ field ∧ field+4 ≤ Listing8StateLayout.endPC mode (region mode l)) :
      field+4 ≤ l.sourceNode+6 ∨ l.sourceNode+10 ≤ field := by
    rcases bounds.nodeOutside with early | late
    · right;omega
    · left;omega
  have helperFields : ∀ writer ∈ Listing8StateLayout.helpers mode (region mode l),
      writer.destination+4 ≤ l.sourceNode+6 ∨ l.sourceNode+10 ≤ writer.destination := by
    intro writer member
    apply outside
    cases mode
    all_goals simp only [Listing8StateLayout.helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl
    all_goals simp [Listing8StateLayout.endPC,Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
      Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize] at coords ⊢ <;> omega
  have packetFields : ∀ writer ∈ Listing8StateLayout.packets mode (region mode l),
      writer.target+4 ≤ l.sourceNode+6 ∨ l.sourceNode+10 ≤ writer.target := by
    intro writer member
    apply outside
    have cursorBefore := Listing8PointerCopies.cursor_before mode l
    have first := endpoint_lower mode l.start (Listing8Prototypes.nodeSpan mode)
    change l.start ≤ secondStart mode l at first
    have after := r.inputAfter
    have input := Listing8InputBounds.positions mode l t bounds.head.input.fields bounds.head.input.joined
    cases mode
    all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
      Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Listing8StateLayout.endPC,Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
      Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,
      Listing8PointerCopies.word,region,StringCodec.sourceField,StringCodec.fieldOffset,Mode.wordBytes] at coords cursorBefore input ⊢ <;> omega
  have frame := congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes))
    (Listing8StateTrace.window mode (region mode l) (local_bounds mode l t r bounds) _
      (Listing8GlobalState.entry mode l t v r owners copies bounds extra seed) (l.sourceNode+6) 4 helperFields packetFields)
  change DwordCode.get (Listing8GlobalState.finish mode l t v extra seed).principal.memory (l.sourceNode+6) =
    DwordCode.get (Listing8GlobalState.entryState mode l t v extra seed).principal.memory (l.sourceNode+6) at frame
  rw [frame]
  exact Listing8HeadValues.tape mode l t v r owners copies bounds.head (Listing8StateImage.backing mode l extra) seed

end SmcTuring.Appendix.Listing8StateValues

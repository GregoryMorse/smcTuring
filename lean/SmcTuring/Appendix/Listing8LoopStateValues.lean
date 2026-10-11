module
public import SmcTuring.Appendix.Listing8LoopStateEntry

public section
namespace SmcTuring.Appendix.Listing8LoopStateValues
open Native Listing8CopyImage Listing8StateGeometry
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopState.Bounds
abbrev Current:=Listing8LoopState.Current

theorem transition (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    MixedMemory.getWord mode (Listing8LoopState.finish mode l t v state).principal.memory (Listing8StateGeometry.region mode l).cursor=
      if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next := by
  have cursor := Listing8LoopStateEntry.cursor mode l t v old b state entry forward current
  have fresh := Listing8LoopStateEntry.new_low mode l t v old b state entry forward current
  have mask := Listing8LoopStateEntry.mask mode l t v old b state entry forward current
    (Listing8StateLayout.maskPC mode (region mode l)+6) (by cases mode <;> simp [Listing8StateFields.maskFields])
  have valid := local_bounds mode l t b.head.input.input.prefixBounds.resources b.state
  have atState := Listing8LoopHead.endpoint mode l t v old b.head state entry forward current.head
  cases mode with
  | x86 =>
    let priorWord : BitVec 32 := v.next
    let new : BitVec 32 := v.newState
    have cursorValue : DwordCode.get (Listing8LoopHead.finish .x86 l t v state).principal.memory (region .x86 l).cursor = priorWord := cursor
    have newValue : DwordCode.get (Listing8LoopHead.finish .x86 l t v state).principal.memory
      (Listing8StateLayout.newPC .x86 (region .x86 l)+6) = new := fresh
    change DwordCode.get (Listing8StateTrace.finish .x86 (region .x86 l) (Listing8LoopHead.finish .x86 l t v state)).principal.memory
      (region .x86 l).cursor = if Listing8LiteralInput.chosen v.rule v.tape then new else priorWord
    rw [Listing8StateMemory.low_cursor .x86 (region .x86 l) valid _ atState,cursorValue,newValue,mask,Listing8StateMemory.selected]
  | x64 =>
    let priorWord : BitVec 64 := v.next
    let new : BitVec 64 := v.newState
    have cursorValue : MixedMemory.getWord .x64 (Listing8LoopHead.finish .x64 l t v state).principal.memory (region .x64 l).cursor = priorWord := cursor
    have lowNew : DwordCode.get (Listing8LoopHead.finish .x64 l t v state).principal.memory
      (Listing8StateLayout.newPC .x64 (region .x64 l)+6) = X64.HalfWords.low new := fresh
    have highNew := Listing8LoopStateEntry.new_high l t v old b state entry forward current
    have highMask := Listing8LoopStateEntry.mask .x64 l t v old b state entry forward current
      (Listing8StateLayout.maskPC .x64 (region .x64 l)+16) (by simp [Listing8StateFields.maskFields])
    have lowOld := (PointerHalves.low_get (Listing8LoopHead.finish .x64 l t v state).principal.memory (region .x64 l).cursor).trans
      (congrArg X64.HalfWords.low cursorValue)
    have highOld := (PointerHalves.high_get (Listing8LoopHead.finish .x64 l t v state).principal.memory (region .x64 l).cursor).trans
      (congrArg X64.HalfWords.high cursorValue)
    rw [PointerHalves.split_get]
    change X64.HalfWords.pack
      (DwordCode.get (Listing8StateTrace.finish .x64 (region .x64 l) (Listing8LoopHead.finish .x64 l t v state)).principal.memory (region .x64 l).cursor)
      (DwordCode.get (Listing8StateTrace.finish .x64 (region .x64 l) (Listing8LoopHead.finish .x64 l t v state)).principal.memory ((region .x64 l).cursor+4)) =
        if Listing8LiteralInput.chosen v.rule v.tape then new else priorWord
    rw [Listing8StateMemory.low_cursor .x64 (region .x64 l) valid _ atState,
      Listing8StateMemory.high_cursor (region .x64 l) valid _ atState,lowOld,highOld,lowNew,highNew,mask,highMask,
      Listing8StateMemory.selected,Listing8StateMemory.selected]
    cases Listing8LiteralInput.chosen v.rule v.tape <;> exact X64.HalfWords.pack_halves _

end SmcTuring.Appendix.Listing8LoopStateValues

module
public import SmcTuring.Appendix.Listing8LoopHeadEntry
public import SmcTuring.Appendix.Listing8LoopHead

public section
namespace SmcTuring.Appendix.Listing8LoopHeadValues
open Native Listing8CopyImage Listing8DirectionGeometry
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopDirection.Bounds
abbrev Current:=Listing8LoopDirection.Current

theorem head_selection (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (takeBack : Bool)
    (encoded : v.direction=(if takeBack then BitVec.allOnes 32 else 0)) :
    MixedMemory.getWord mode (Listing8LoopHead.finish mode l t v state).principal.memory l.input.cursor=
      if Listing8LiteralInput.chosen v.rule v.tape then (if takeBack then v.back else v.forward)
      else Arithmetic.encodeNat mode l.input.head := by
  have neighborChosen:=Listing8LoopDirectionSelection.selected mode l t v old b state entry forward current takeBack encoded
  have cursor := Listing8LoopHeadEntry.cursor mode l t v old b state entry forward current
  have mask := Listing8LoopHeadEntry.mask mode l t v old b state entry forward current
    (Listing8DirectionLayout.maskPC mode (region mode l)+6) (by cases mode <;> simp [Listing8HeadGeometry.maskFields])
  have tail := Listing8HeadGeometry.tail_bounds mode l t b.direction
  have atTail := Listing8LoopDirection.endpoint mode l t v old b state entry forward current
  cases mode with
  | x86 =>
    let neighbor : BitVec 32 := if takeBack then v.back else v.forward
    let original : BitVec 32 := Arithmetic.encodeNat .x86 l.input.head
    change DwordCode.get (Listing8HeadTailTrace.finish .x86 (region .x86 l)
      (Listing8LoopDirection.finish .x86 l t v state)).principal.memory (region .x86 l).cursor =
        if Listing8LiteralInput.chosen v.rule v.tape then neighbor else original
    rw [Listing8HeadTailMemory.low_cursor .x86 (region .x86 l) tail _ atTail]
    have selectedValue : DwordCode.get (Listing8LoopDirection.finish .x86 l t v state).principal.memory
      (Listing8DirectionLayout.directionPC .x86 (region .x86 l)+6) = neighbor := neighborChosen
    have cursorValue : DwordCode.get (Listing8LoopDirection.finish .x86 l t v state).principal.memory l.input.cursor = original := cursor
    simp only [region] at selectedValue cursorValue mask ⊢
    rw [selectedValue,cursorValue,mask,Listing8HeadTailMemory.selected]
  | x64 =>
    let neighbor : BitVec 64 := if takeBack then v.back else v.forward
    let original : BitVec 64 := Arithmetic.encodeNat .x64 l.input.head
    have selectedValue : Listing8DirectionSelected.value .x64
      (Listing8LoopDirection.finish .x64 l t v state).principal.memory
      (Listing8DirectionLayout.directionPC .x64 (region .x64 l)) = neighbor := neighborChosen
    have cursorValue : MixedMemory.getWord .x64
      (Listing8LoopDirection.finish .x64 l t v state).principal.memory l.input.cursor = original := cursor
    have highMask := Listing8LoopHeadEntry.mask .x64 l t v old b state entry forward current
      (Listing8DirectionLayout.maskPC .x64 (region .x64 l)+16) (by simp [Listing8HeadGeometry.maskFields])
    have lowSelected := congrArg X64.HalfWords.low selectedValue
    have highSelected := congrArg X64.HalfWords.high selectedValue
    simp only [Listing8DirectionSelected.value,X64.HalfWords.low_pack] at lowSelected
    simp only [Listing8DirectionSelected.value,X64.HalfWords.high_pack] at highSelected
    have lowCursor := (PointerHalves.low_get (Listing8LoopDirection.finish .x64 l t v state).principal.memory l.input.cursor).trans
      (congrArg X64.HalfWords.low cursorValue)
    have highCursor := (PointerHalves.high_get (Listing8LoopDirection.finish .x64 l t v state).principal.memory l.input.cursor).trans
      (congrArg X64.HalfWords.high cursorValue)
    rw [PointerHalves.split_get]
    change X64.HalfWords.pack
      (DwordCode.get (Listing8HeadTailTrace.finish .x64 (region .x64 l) (Listing8LoopDirection.finish .x64 l t v state)).principal.memory (region .x64 l).cursor)
      (DwordCode.get (Listing8HeadTailTrace.finish .x64 (region .x64 l) (Listing8LoopDirection.finish .x64 l t v state)).principal.memory ((region .x64 l).cursor+4)) =
        if Listing8LiteralInput.chosen v.rule v.tape then neighbor else original
    rw [Listing8HeadTailMemory.low_cursor .x64 (region .x64 l) tail _ atTail,
      Listing8HeadTailMemory.high_cursor (region .x64 l) tail _ atTail]
    simp only [region] at lowSelected highSelected lowCursor highCursor mask highMask ⊢
    rw [lowSelected,highSelected,lowCursor,highCursor,mask,highMask,
      Listing8HeadTailMemory.selected,Listing8HeadTailMemory.selected]
    cases Listing8LiteralInput.chosen v.rule v.tape <;> exact X64.HalfWords.pack_halves _

end SmcTuring.Appendix.Listing8LoopHeadValues

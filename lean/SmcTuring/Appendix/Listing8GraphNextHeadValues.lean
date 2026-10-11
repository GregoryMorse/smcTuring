module
public import SmcTuring.Appendix.Listing8GraphNextHeadEntry

public section
namespace SmcTuring.Appendix.Listing8GraphNextHeadValues
open Native Listing8CopyImage Listing8DirectionGeometry Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem head_selection (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      if Listing8LiteralInput.chosen (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape then (if (g.rules target).takeBack then (liveValues mode origin g node rule target).back else (liveValues mode origin g node rule target).forward)
      else Arithmetic.encodeNat mode (nextLayout mode origin l g node rule target).sourceNode := by
  let v:=liveValues mode origin g node rule target
  let takeBack:=(g.rules target).takeBack
  have neighborChosen:=Listing8GraphNextDirectionSelection.selected mode origin l t g node rule target ctx selected memory seed
  have cursor := Listing8GraphNextHeadEntry.cursor mode origin l t g node rule target ctx selected memory seed
  have mask := Listing8GraphNextHeadEntry.mask mode origin l t g node rule target ctx selected memory seed
    (Listing8DirectionLayout.maskPC mode (region mode l)+6) (by cases mode <;> simp [Listing8HeadGeometry.maskFields])
  have tail := Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head
  have entry := Listing8GraphNextDirection.endpoint mode origin l t g node rule target ctx selected memory seed
  cases mode with
  | x86 =>
    let neighbor : BitVec 32 := if takeBack then v.back else v.forward
    let original : BitVec 32 := Arithmetic.encodeNat .x86 (nextLayout .x86 origin l g node rule target).sourceNode
    change DwordCode.get (Listing8HeadTailTrace.finish .x86 (region .x86 l)
      (Listing8GraphNextDirection.finish .x86 origin l t g node rule target memory seed)).principal.memory (region .x86 l).cursor =
        if Listing8LiteralInput.chosen v.rule v.tape then neighbor else original
    rw [Listing8HeadTailMemory.low_cursor .x86 (region .x86 l) tail _ entry]
    have selectedValue : DwordCode.get (Listing8GraphNextDirection.finish .x86 origin l t g node rule target memory seed).principal.memory
      (Listing8DirectionLayout.directionPC .x86 (region .x86 l)+6) = neighbor := neighborChosen
    have cursorValue : DwordCode.get (Listing8GraphNextDirection.finish .x86 origin l t g node rule target memory seed).principal.memory l.input.cursor = original := cursor
    simp only [region] at selectedValue cursorValue mask ⊢
    rw [selectedValue,cursorValue,mask,Listing8HeadTailMemory.selected]
  | x64 =>
    let neighbor : BitVec 64 := if takeBack then v.back else v.forward
    let original : BitVec 64 := Arithmetic.encodeNat .x64 (nextLayout .x64 origin l g node rule target).sourceNode
    have selectedValue : Listing8DirectionSelected.value .x64
      (Listing8GraphNextDirection.finish .x64 origin l t g node rule target memory seed).principal.memory
      (Listing8DirectionLayout.directionPC .x64 (region .x64 l)) = neighbor := neighborChosen
    have cursorValue : MixedMemory.getWord .x64
      (Listing8GraphNextDirection.finish .x64 origin l t g node rule target memory seed).principal.memory l.input.cursor = original := cursor
    have highMask := Listing8GraphNextHeadEntry.mask .x64 origin l t g node rule target ctx selected memory seed
      (Listing8DirectionLayout.maskPC .x64 (region .x64 l)+16) (by simp [Listing8HeadGeometry.maskFields])
    have lowSelected := congrArg X64.HalfWords.low selectedValue
    have highSelected := congrArg X64.HalfWords.high selectedValue
    simp only [Listing8DirectionSelected.value,X64.HalfWords.low_pack] at lowSelected
    simp only [Listing8DirectionSelected.value,X64.HalfWords.high_pack] at highSelected
    have lowCursor := (PointerHalves.low_get (Listing8GraphNextDirection.finish .x64 origin l t g node rule target memory seed).principal.memory l.input.cursor).trans
      (congrArg X64.HalfWords.low cursorValue)
    have highCursor := (PointerHalves.high_get (Listing8GraphNextDirection.finish .x64 origin l t g node rule target memory seed).principal.memory l.input.cursor).trans
      (congrArg X64.HalfWords.high cursorValue)
    rw [PointerHalves.split_get]
    change X64.HalfWords.pack
      (DwordCode.get (Listing8HeadTailTrace.finish .x64 (region .x64 l) (Listing8GraphNextDirection.finish .x64 origin l t g node rule target memory seed)).principal.memory (region .x64 l).cursor)
      (DwordCode.get (Listing8HeadTailTrace.finish .x64 (region .x64 l) (Listing8GraphNextDirection.finish .x64 origin l t g node rule target memory seed)).principal.memory ((region .x64 l).cursor+4)) =
        if Listing8LiteralInput.chosen v.rule v.tape then neighbor else original
    rw [Listing8HeadTailMemory.low_cursor .x64 (region .x64 l) tail _ entry,
      Listing8HeadTailMemory.high_cursor (region .x64 l) tail _ entry]
    simp only [region] at lowSelected highSelected lowCursor highCursor mask highMask ⊢
    rw [lowSelected,highSelected,lowCursor,highCursor,mask,highMask,
      Listing8HeadTailMemory.selected,Listing8HeadTailMemory.selected]
    cases Listing8LiteralInput.chosen v.rule v.tape <;> exact X64.HalfWords.pack_halves _

theorem logical_head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode (Listing8GraphStep.updated g node rule)
        (Listing8GraphStep.nextNode g node rule) target)) := by
  rw [head_selection mode origin l t g node rule target ctx selected memory seed]
  exact Listing8GraphStep.head_pointer mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target

end SmcTuring.Appendix.Listing8GraphNextHeadValues

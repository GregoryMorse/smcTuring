module
public import SmcTuring.Appendix.Listing8GraphNextStateEntry

public section
namespace SmcTuring.Appendix.Listing8GraphNextStateValues
open Native Listing8CopyImage Listing8StateGeometry Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      if Listing8LiteralInput.chosen (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape then (liveValues mode origin g node rule target).newState else (liveValues mode origin g node rule target).next := by
  let v:=liveValues mode origin g node rule target
  have cursor := Listing8GraphNextStateEntry.cursor mode origin l t g node rule target ctx selected memory seed
  have fresh := Listing8GraphNextStateEntry.new_low mode origin l t g node rule target ctx selected memory seed
  have mask := Listing8GraphNextStateEntry.mask mode origin l t g node rule target ctx selected memory seed
    (Listing8StateLayout.maskPC mode (region mode l)+6) (by cases mode <;> simp [Listing8StateFields.maskFields])
  have valid := local_bounds mode l t ctx.resources ctx.body.state
  have entry := Listing8GraphNextHead.endpoint mode origin l t g node rule target ctx selected memory seed
  cases mode with
  | x86 =>
    let old : BitVec 32 := v.next
    let new : BitVec 32 := v.newState
    have cursorValue : DwordCode.get (Listing8GraphNextHead.finish .x86 origin l t g node rule target memory seed).principal.memory (region .x86 l).cursor = old := cursor
    have newValue : DwordCode.get (Listing8GraphNextHead.finish .x86 origin l t g node rule target memory seed).principal.memory
      (Listing8StateLayout.newPC .x86 (region .x86 l)+6) = new := fresh
    change DwordCode.get (Listing8StateTrace.finish .x86 (region .x86 l) (Listing8GraphNextHead.finish .x86 origin l t g node rule target memory seed)).principal.memory
      (region .x86 l).cursor = if Listing8LiteralInput.chosen v.rule v.tape then new else old
    rw [Listing8StateMemory.low_cursor .x86 (region .x86 l) valid _ entry,cursorValue,newValue,mask,Listing8StateMemory.selected]
  | x64 =>
    let old : BitVec 64 := v.next
    let new : BitVec 64 := v.newState
    have cursorValue : MixedMemory.getWord .x64 (Listing8GraphNextHead.finish .x64 origin l t g node rule target memory seed).principal.memory (region .x64 l).cursor = old := cursor
    have lowNew : DwordCode.get (Listing8GraphNextHead.finish .x64 origin l t g node rule target memory seed).principal.memory
      (Listing8StateLayout.newPC .x64 (region .x64 l)+6) = X64.HalfWords.low new := fresh
    have highNew := Listing8GraphNextStateEntry.new_high origin l t g node rule target ctx selected memory seed
    have highMask := Listing8GraphNextStateEntry.mask .x64 origin l t g node rule target ctx selected memory seed
      (Listing8StateLayout.maskPC .x64 (region .x64 l)+16) (by simp [Listing8StateFields.maskFields])
    have lowOld := (PointerHalves.low_get (Listing8GraphNextHead.finish .x64 origin l t g node rule target memory seed).principal.memory (region .x64 l).cursor).trans
      (congrArg X64.HalfWords.low cursorValue)
    have highOld := (PointerHalves.high_get (Listing8GraphNextHead.finish .x64 origin l t g node rule target memory seed).principal.memory (region .x64 l).cursor).trans
      (congrArg X64.HalfWords.high cursorValue)
    rw [PointerHalves.split_get]
    change X64.HalfWords.pack
      (DwordCode.get (Listing8StateTrace.finish .x64 (region .x64 l) (Listing8GraphNextHead.finish .x64 origin l t g node rule target memory seed)).principal.memory (region .x64 l).cursor)
      (DwordCode.get (Listing8StateTrace.finish .x64 (region .x64 l) (Listing8GraphNextHead.finish .x64 origin l t g node rule target memory seed)).principal.memory ((region .x64 l).cursor+4)) =
        if Listing8LiteralInput.chosen v.rule v.tape then new else old
    rw [Listing8StateMemory.low_cursor .x64 (region .x64 l) valid _ entry,
      Listing8StateMemory.high_cursor (region .x64 l) valid _ entry,lowOld,highOld,lowNew,highNew,mask,highMask,
      Listing8StateMemory.selected,Listing8StateMemory.selected]
    cases Listing8LiteralInput.chosen v.rule v.tape <;> exact X64.HalfWords.pack_halves _

theorem state_label (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (query : Option (Fin g.transitions)) :
    statePC mode origin (Listing8GraphStep.updated g node rule) query=statePC mode origin g query := by
  cases query <;> rfl

theorem logical_transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (statePC mode origin g (Listing8GraphStep.nextRule (Listing8GraphStep.updated g node rule)
        (Listing8GraphStep.nextNode g node rule) target)) := by
  rw [transition mode origin l t g node rule target ctx selected memory seed]
  exact (Listing8GraphStep.rule_pointer mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target).trans
    (congrArg (Arithmetic.encodeNat mode) (state_label mode origin g node rule
      (Listing8GraphStep.nextRule (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)))

end SmcTuring.Appendix.Listing8GraphNextStateValues

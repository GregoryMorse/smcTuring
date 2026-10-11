module
public import SmcTuring.Appendix.Listing8HeadImage

public section
namespace SmcTuring.Appendix.Listing8GlobalHead
open Native Listing8CopyImage Listing8DirectionGeometry
abbrev Targets := Listing8PointerCopies.Targets
@[expose] def entryState (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalDirection.finish mode l t v extra seed
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8HeadTailTrace.finish mode (region mode l) (entryState mode l t v extra seed)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalDirection.program mode l t v extra seed ++
    Listing8HeadTailTrace.program mode (region mode l) (entryState mode l t v extra seed)

theorem entry (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (entryState mode l t v extra seed).principal.pc = Arithmetic.encodeNat mode (Listing8DirectionLayout.selectionEnd mode (region mode l)) :=
  Listing8DirectionTrace.endpoint mode (region mode l) bounds.capacity
    (Listing8GlobalDirection.entryState mode l t v extra seed) (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed)

/-- The original global initialized image supplies all actual fetches
through input, selection, cursor-difference, mask and head XOR. -/
theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (initial mode l v
      (Listing8PointerImage.backing mode l t (Listing8DirectionImage.backing mode l extra)) seed)
      (program mode l t v extra seed) (finish mode l t v extra seed) := by
  have first := Listing8GlobalDirection.trace mode l t v r owners copies bounds extra seed
  have rest := Listing8HeadTailTrace.trace mode (region mode l) (Listing8HeadGeometry.tail_bounds mode l t bounds)
    (entryState mode l t v extra seed) (entry mode l t v r owners copies bounds extra seed)
    (Listing8HeadImage.xor_current mode l t v r owners copies bounds extra seed)
    (Listing8HeadImage.headers_current mode l t v r owners copies bounds extra seed)
  exact StringDword.trace_append mode first rest

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode l t v extra seed).length = if mode = .x86 then 113 else 145 := by
  rw [program,List.length_append,Listing8GlobalDirection.instruction_count,Listing8HeadTailTrace.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l t v extra seed).principal.pc = Arithmetic.encodeNat mode (l.start+(if mode = .x86 then 597 else 932)) := by
  have last := Listing8HeadTailTrace.endpoint mode (region mode l) (Listing8HeadGeometry.tail_bounds mode l t bounds)
    (entryState mode l t v extra seed) (entry mode l t v r owners copies bounds extra seed)
  have input := Listing8InputBounds.positions mode l t bounds.input.fields bounds.input.joined
  have coords := (Listing8DirectionLayout.positions mode (region mode l)).2.2.2.2.2.2.2
  change (Listing8HeadTailTrace.finish mode (region mode l) (entryState mode l t v extra seed)).principal.pc = _
  rw [last]
  congr 1
  rw [coords]
  change Listing8LiteralInput.endPC mode l.input+(if mode = .x86 then 91 else 202) = _
  rw [input.2.1]
  cases mode <;> rfl

theorem registers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l t v extra seed).principal.stack = seed.principal.stack ∧
    (finish mode l t v extra seed).principal.carry = false ∧
    (finish mode l t v extra seed).sourceIndex = seed.sourceIndex ∧
    (finish mode l t v extra seed).destinationIndex = seed.destinationIndex ∧
    (finish mode l t v extra seed).backwards = false ∧
    (finish mode l t v extra seed).principal.accumulator = DwordCode.lift mode
      (DwordCode.low mode (Listing8PointerImage.ownerFinish mode l t v (Listing8DirectionImage.backing mode l extra) seed).principal.accumulator) := by
  have previous := Listing8GlobalDirection.registers mode l t v r owners copies bounds extra seed
  have last := Listing8HeadTailTrace.registers mode (region mode l) (Listing8HeadGeometry.tail_bounds mode l t bounds)
    (entryState mode l t v extra seed) (entry mode l t v r owners copies bounds extra seed)
  refine ⟨last.2.1.trans previous.1,last.2.2.1,last.2.2.2.1.trans previous.2.2.1,
    last.2.2.2.2.1.trans previous.2.2.2.1,last.2.2.2.2.2.trans previous.2.2.2.2.1,?_⟩
  rw [show (finish mode l t v extra seed).principal.accumulator = _ from last.1,
    entryState,previous.2.2.2.2.2,DwordCode.low_lift]

end SmcTuring.Appendix.Listing8GlobalHead

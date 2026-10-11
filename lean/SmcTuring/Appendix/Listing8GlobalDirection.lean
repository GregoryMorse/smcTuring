module
public import SmcTuring.Appendix.Listing8DirectionImage

public section
namespace SmcTuring.Appendix.Listing8GlobalDirection
open Native Listing8CopyImage Listing8DirectionGeometry
abbrev Targets := Listing8PointerCopies.Targets
@[expose] def entryState (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalInput.finish mode l t v (Listing8DirectionImage.backing mode l extra) seed
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8DirectionTrace.finish mode (region mode l) (entryState mode l t v extra seed)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalInput.program mode l t v ++
    Listing8DirectionTrace.program mode (region mode l) (entryState mode l t v extra seed)

theorem entry (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (entryState mode l t v extra seed).principal.pc = Arithmetic.encodeNat mode (region mode l).start :=
  Listing8GlobalInput.endpoint mode l t v r owners copies bounds.input (Listing8DirectionImage.backing mode l extra) seed

theorem helper_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (entryState mode l t v extra seed).principal.memory (region mode l).start
      (DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l))).length =
      DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l)) := by
  have upper : (region mode l).start+(DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l))).length ≤
      Listing8DirectionLayout.selectionEnd mode (region mode l) := by
    rw [helper_bytes]
    have coords := Listing8DirectionLayout.positions mode (region mode l)
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  change ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v (Listing8DirectionImage.backing mode l extra) seed).principal.memory _ _ = _
  rw [Listing8GlobalWindows.input mode l t v r owners copies bounds.input _ seed _ _
    (input_window mode l t bounds _ _ (Nat.le_refl _) upper),Listing8GlobalInput.entryState,
    Listing8GlobalWindows.pointers mode l t v r owners copies
      (Listing8DirectionImage.backing mode l extra) seed (region mode l).start
      (DwordMixedSequence.bytes mode (Listing8DirectionLayout.helpers mode (region mode l))).length (Nat.le_refl _)
      (Or.inr (Nat.le_trans upper (positions mode l t bounds).2.2))
      (fun writer member => Or.inr (pointer_helpers mode l t bounds writer member))]
  exact Listing8DirectionImage.initial_helpers mode l t v r bounds extra

theorem arithmetic_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordPackets.Intact mode (Listing8DirectionLayout.arithmetic mode (region mode l))
      (entryState mode l t v extra seed).principal.memory := by
  intro reader member
  have spans := arithmetic_header_bounds mode l reader member
  change ByteMemory.bytesAt (Listing8GlobalInput.finish mode l t v (Listing8DirectionImage.backing mode l extra) seed).principal.memory reader.pc 6 = _
  rw [Listing8GlobalWindows.input mode l t v r owners copies bounds.input _ seed reader.pc 6
    (input_window mode l t bounds _ _ spans.1 spans.2),Listing8GlobalInput.entryState,
    Listing8GlobalWindows.pointers mode l t v r owners copies _ seed reader.pc 6 spans.1
      (Or.inr (Nat.le_trans spans.2 (positions mode l t bounds).2.2))
      (pointer_headers mode l t bounds reader member)]
  exact Listing8DirectionImage.initial_headers mode l t v r bounds extra reader member

/-- One initialized image supplies the actual input and direction-selection
execution. Every helper packet and mutable arithmetic fetch is derived. -/
theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (initial mode l v
      (Listing8PointerImage.backing mode l t (Listing8DirectionImage.backing mode l extra)) seed)
      (program mode l t v extra seed) (finish mode l t v extra seed) := by
  have first := Listing8GlobalInput.trace mode l t v r owners copies bounds.input (Listing8DirectionImage.backing mode l extra) seed
  have rest := Listing8DirectionTrace.trace mode (region mode l) bounds.capacity (entryState mode l t v extra seed)
    (entry mode l t v r owners copies bounds extra seed) (helper_current mode l t v r owners copies bounds extra seed)
    (arithmetic_current mode l t v r owners copies bounds extra seed)
  exact StringDword.trace_append mode first rest

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode l t v extra seed).length = if mode = .x86 then 108 else 135 := by
  rw [program,List.length_append,Listing8GlobalInput.instruction_count,Listing8DirectionTrace.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l t v extra seed).principal.pc = Arithmetic.encodeNat mode (l.start+(if mode = .x86 then 559 else 856)) := by
  have last := Listing8DirectionTrace.endpoint mode (region mode l) bounds.capacity (entryState mode l t v extra seed)
    (entry mode l t v r owners copies bounds extra seed)
  have input := Listing8InputBounds.positions mode l t bounds.input.fields bounds.input.joined
  have coords := (Listing8DirectionLayout.positions mode (region mode l)).2.2.2.2.1
  change (Listing8DirectionTrace.finish mode (region mode l) (entryState mode l t v extra seed)).principal.pc = _
  rw [last]
  congr 1
  rw [coords]
  change Listing8LiteralInput.endPC mode l.input+(if mode = .x86 then 53 else 126) = _
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
  have previous := Listing8GlobalInput.registers mode l t v r owners copies bounds.input (Listing8DirectionImage.backing mode l extra) seed
  have last := Listing8DirectionTrace.registers mode (region mode l) bounds.capacity (entryState mode l t v extra seed)
    (entry mode l t v r owners copies bounds extra seed)
  refine ⟨last.2.1.trans previous.1,last.2.2.1,last.2.2.2.1.trans previous.2.2.1,
    last.2.2.2.2.1.trans previous.2.2.2.1,last.2.2.2.2.2.trans previous.2.2.2.2.1,?_⟩
  rw [show (finish mode l t v extra seed).principal.accumulator = _ from last.1,
    entryState,previous.2.2.2.2.2,DwordCode.low_lift]

end SmcTuring.Appendix.Listing8GlobalDirection

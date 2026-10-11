module
public import SmcTuring.Appendix.Listing8InputBounds
public import SmcTuring.Appendix.Listing8InputMaskEffects
public import SmcTuring.Native.StringMixed

public section
namespace SmcTuring.Appendix.Listing8GlobalInput
open Native Listing8CopyImage
abbrev Targets := Listing8PointerCopies.Targets

/-- Initial label/field geometry only. Future cursor/tape values, images,
readiness, fetched forms and execution are not hypotheses. -/
structure Bounds (mode : Mode) (l : Layout) (t : Targets) : Prop where
  fields : Listing8InputBounds.Fields mode l
  joined : l.input.start = Listing8PointerCopies.endPC mode l
  targetsAfter : ∀ pc ∈ [t.state,t.back,t.forward], Listing8LiteralInput.endPC mode l.input ≤ pc
  nodeTargets : ∀ lay ∈ Listing8PointerCopies.layouts mode l t,
    lay.destination+4 ≤ l.sourceNode ∨ l.sourceNode+Listing8Prototypes.nodeSpan mode ≤ lay.destination

@[expose] def entryState (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8PointerImage.finish mode l t v extra seed
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :=
  Listing8PointerImage.program mode l t v ++
    (Listing8LiteralComposition.program mode l.input v.rule v.tape v.fresh).map (StringMixed.canonical mode)
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  let state := entryState mode l t v extra seed
  {state with principal := Listing8LiteralComposition.finish mode l.input v.rule v.tape v.fresh state.principal}

theorem entry (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (entryState mode l t v extra seed).principal.pc = Arithmetic.encodeNat mode l.input.start :=
  Listing8PointerImage.endpoint mode l t v r owners copies bounds.joined extra seed

theorem input_image (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8InputMask.Intact mode l.input v.rule v.tape force v.fresh force
      (entryState mode l t v extra seed).principal.memory :=
  Listing8PointerValues.input_image mode l t v r owners copies bounds.targetsAfter extra seed

theorem cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (entryState mode l t v extra seed).principal.memory l.input.cursor =
      Arithmetic.encodeNat mode l.input.head := by
  rw [bounds.fields.cursorLabel,bounds.fields.headLabel]
  exact Listing8PointerValues.input_cursor mode l t v r owners copies extra seed

theorem symbol (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (entryState mode l t v extra seed).principal.memory (l.input.head+6) = v.tape := by
  rw [bounds.fields.headLabel]
  exact Listing8PointerValues.tape_symbol mode l t v r owners copies bounds.nodeTargets extra seed

/-- The actual printed input reset/M13/M14/comparison/M15/update follows
the executed initializer and pointer copies in the same state/decoder.
The rule, tape, cursor and complete input image are all derived. -/
theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (initial mode l v (Listing8PointerImage.backing mode l t extra) seed)
      (program mode l t v) (finish mode l t v extra seed) := by
  have prefixTrace := Listing8PointerImage.trace mode l t v r owners copies bounds.joined extra seed
  have actualInput := Listing8InputMask.trace mode l.input v.rule v.tape force v.fresh force r.inputFits
    (Listing8InputBounds.masks mode l bounds.fields)
    (Listing8InputBounds.update mode l t bounds.fields bounds.joined r)
    (Listing8InputBounds.outside mode l t bounds.fields bounds.joined r)
    (entryState mode l t v extra seed).principal (entry mode l t v r owners copies bounds extra seed)
    (input_image mode l t v r owners copies bounds extra seed) (cursor mode l t v r owners copies bounds extra seed)
  exact StringDword.trace_append mode prefixTrace (StringMixed.trace mode _ _ _ actualInput)

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :
    (program mode l t v).length = if mode = .x86 then 101 else 118 := by
  rw [program,List.length_append,List.length_map,Listing8PointerImage.instruction_count,
    Listing8LiteralComposition.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l t v extra seed).principal.pc = Arithmetic.encodeNat mode (Listing8LiteralInput.endPC mode l.input) :=
  Listing8InputMaskEffects.endpoint mode l.input v.rule v.tape force v.fresh force r.inputFits
    (Listing8InputBounds.masks mode l bounds.fields)
    (Listing8InputBounds.update mode l t bounds.fields bounds.joined r)
    (Listing8InputBounds.outside mode l t bounds.fields bounds.joined r) _
    (entry mode l t v r owners copies bounds extra seed) (input_image mode l t v r owners copies bounds extra seed)
    (cursor mode l t v r owners copies bounds extra seed) (symbol mode l t v r owners copies bounds extra seed)

theorem tape_value (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (finish mode l t v extra seed).principal.memory (l.input.head+6) =
      if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape :=
  Listing8InputMask.tape_value mode l.input v.rule v.tape force v.fresh force r.inputFits
    (Listing8InputBounds.masks mode l bounds.fields)
    (Listing8InputBounds.update mode l t bounds.fields bounds.joined r)
    (Listing8InputBounds.outside mode l t bounds.fields bounds.joined r) _
    (entry mode l t v r owners copies bounds extra seed) (input_image mode l t v r owners copies bounds extra seed)
    (cursor mode l t v r owners copies bounds extra seed) (symbol mode l t v r owners copies bounds extra seed)

theorem retained (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    InputUpdate.Intact mode (Listing8LiteralInput.updateLayout mode l.input)
      (CursorEffects.delta v.tape v.fresh (Listing8LiteralInput.chosen v.rule v.tape))
      v.fresh (Listing8LiteralInput.chosen v.rule v.tape) (finish mode l t v extra seed).principal.memory :=
  Listing8InputMask.retained mode l.input v.rule v.tape force v.fresh force r.inputFits
    (Listing8InputBounds.masks mode l bounds.fields)
    (Listing8InputBounds.update mode l t bounds.fields bounds.joined r)
    (Listing8InputBounds.outside mode l t bounds.fields bounds.joined r) _
    (entry mode l t v r owners copies bounds extra seed) (input_image mode l t v r owners copies bounds extra seed)
    (cursor mode l t v r owners copies bounds extra seed) (symbol mode l t v r owners copies bounds extra seed)

theorem registers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l t v extra seed).principal.stack = seed.principal.stack ∧
    (finish mode l t v extra seed).principal.carry = false ∧
    (finish mode l t v extra seed).sourceIndex = seed.sourceIndex ∧
    (finish mode l t v extra seed).destinationIndex = seed.destinationIndex ∧
    (finish mode l t v extra seed).backwards = false ∧
    (finish mode l t v extra seed).principal.accumulator =
      DwordCode.lift mode (DwordCode.low mode (Listing8PointerImage.ownerFinish mode l t v extra seed).principal.accumulator) := by
  have prior := Listing8PointerValues.registers mode l t v r owners copies extra seed
  have result := Listing8InputMaskEffects.registers mode l.input v.rule v.tape force v.fresh force r.inputFits
    (Listing8InputBounds.masks mode l bounds.fields)
    (Listing8InputBounds.update mode l t bounds.fields bounds.joined r)
    (Listing8InputBounds.outside mode l t bounds.fields bounds.joined r) _
    (entry mode l t v r owners copies bounds extra seed) (input_image mode l t v r owners copies bounds extra seed)
    (cursor mode l t v r owners copies bounds extra seed) (symbol mode l t v r owners copies bounds extra seed)
  refine ⟨result.2.1.trans prior.1,result.2.2,prior.2.2.1,prior.2.2.2.1,prior.2.2.2.2.1,?_⟩
  rw [show (finish mode l t v extra seed).principal.accumulator = _ from result.1,
    entryState,prior.2.2.2.2.2,DwordCode.low_lift]

end SmcTuring.Appendix.Listing8GlobalInput

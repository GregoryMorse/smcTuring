module
public import SmcTuring.Appendix.Listing8DirectionBounds

public section
namespace SmcTuring.Appendix.Listing8DirectionTrace
open Native Listing8DirectionLayout
@[expose] def helperFinish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringDwordSequence.finish mode (helpers mode l) state
@[expose] def finish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  let current := helperFinish mode l state
  {current with principal := DwordPackets.finish mode (arithmetic mode l) current.principal}
@[expose] def program (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringDwordSequence.program mode (helpers mode l) ++
    DwordPackets.program mode (arithmetic mode l) (helperFinish mode l state).principal

theorem helper_endpoint (mode : Mode) (l : Layout) (capacity : endPC mode l < 2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    (helperFinish mode l state).principal.pc = Arithmetic.encodeNat mode (backPC mode l) := by
  have endpoint := StringDwordSequence.endpoint mode (helpers mode l) l.start (helper_chain mode l)
    (Listing8DirectionBounds.helper_valid mode l capacity) state entry
  rw [helpers_length] at endpoint
  cases mode <;> simpa [helperFinish,backPC,copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc] using endpoint

theorem helper_headers (mode : Mode) (l : Layout) (capacity : endPC mode l < 2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start)
    (intact : DwordPackets.Intact mode (arithmetic mode l) state.principal.memory) :
    DwordPackets.Intact mode (arithmetic mode l) (helperFinish mode l state).principal.memory := by
  intro reader member
  rw [DwordPackets.Current,helperFinish,StringDwordSequence.window mode (helpers mode l) l.start (helper_chain mode l)
    (Listing8DirectionBounds.helper_valid mode l capacity) state entry reader.pc 6
    (fun writer writerMember => Listing8DirectionBounds.helpers_outside_headers mode l writer writerMember reader member)]
  exact intact reader member

/-- The initial helper image and arithmetic headers derive all current
fetches through duplication, corresponding-half copy and AND/NOT/AND/OR. -/
theorem trace (mode : Mode) (l : Layout) (capacity : endPC mode l < 2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start)
    (helperImage : ByteMemory.bytesAt state.principal.memory l.start (DwordMixedSequence.bytes mode (helpers mode l)).length =
      DwordMixedSequence.bytes mode (helpers mode l))
    (headers : DwordPackets.Intact mode (arithmetic mode l) state.principal.memory) :
    StringDword.Trace mode state (program mode l state) (finish mode l state) := by
  have first := StringDwordSequence.trace mode (helpers mode l) l.start (helper_chain mode l)
    (Listing8DirectionBounds.helper_valid mode l capacity) (Listing8DirectionBounds.helper_frames mode l) state entry
    (DwordMixedSequence.intact_of_bytes mode (helpers mode l) l.start (helper_chain mode l) state.principal.memory helperImage)
  have rest := DwordPackets.trace mode (arithmetic mode l) (backPC mode l) (arithmetic_chain mode l)
    (Listing8DirectionBounds.arithmetic_valid mode l capacity) (Listing8DirectionBounds.arithmetic_frames mode l)
    (helperFinish mode l state) (helper_endpoint mode l capacity state entry)
    (helper_headers mode l capacity state entry headers)
  exact StringDword.trace_append mode first rest

theorem instruction_count (mode : Mode) (l : Layout) (state : StringExecution.State mode) :
    (program mode l state).length = if mode = .x86 then 7 else 17 := by
  rw [program,List.length_append,DwordPackets.instruction_count,arithmetic_length]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (l : Layout) (capacity : endPC mode l < 2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    (finish mode l state).principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l) := by
  have last := DwordPackets.endpoint mode (arithmetic mode l) (backPC mode l) (arithmetic_chain mode l)
    (Listing8DirectionBounds.arithmetic_valid mode l capacity) (helperFinish mode l state).principal
    (helper_endpoint mode l capacity state entry)
  change (DwordPackets.finish mode (arithmetic mode l) (helperFinish mode l state).principal).pc = _
  rw [last]
  congr 1
  cases mode <;> simp [arithmetic,group,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,
    selectionEnd,combinedPC,forwardPC,notPC,halves,Listing8PointerCopies.halfCount,Nat.add_assoc]

theorem registers (mode : Mode) (l : Layout) (capacity : endPC mode l < 2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    (finish mode l state).principal.accumulator = DwordCode.lift mode (DwordCode.low mode state.principal.accumulator) ∧
    (finish mode l state).principal.stack = state.principal.stack ∧ (finish mode l state).principal.carry = false ∧
    (finish mode l state).sourceIndex = state.sourceIndex ∧ (finish mode l state).destinationIndex = state.destinationIndex ∧
    (finish mode l state).backwards = state.backwards := by
  have helper := StringDwordSequence.registers mode (helpers mode l) l.start (helper_chain mode l)
    (Listing8DirectionBounds.helper_valid mode l capacity) state entry
  have last := DwordPackets.registers mode (arithmetic mode l) (helperFinish mode l state).principal
  have nonempty : (helpers mode l).length ≠ 0 := by rw [helpers_length];cases mode <;> decide
  refine ⟨last.1.trans (by simpa only [helperFinish,ite_eq_right nonempty] using helper.2.2.1),last.2.trans helper.1,?_,rfl,rfl,rfl⟩
  cases mode <;> rfl

theorem window (mode : Mode) (l : Layout) (capacity : endPC mode l < 2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start)
    (observed count : Nat)
    (helperOutside : ∀ writer ∈ helpers mode l, writer.destination+4 ≤ observed ∨ observed+count ≤ writer.destination)
    (packetOutside : ∀ writer ∈ arithmetic mode l, writer.target+4 ≤ observed ∨ observed+count ≤ writer.target) :
    ByteMemory.bytesAt (finish mode l state).principal.memory observed count = ByteMemory.bytesAt state.principal.memory observed count := by
  rw [finish,DwordPackets.window mode (arithmetic mode l) (backPC mode l) (arithmetic_chain mode l)
    (Listing8DirectionBounds.arithmetic_valid mode l capacity) (helperFinish mode l state).principal
    (helper_endpoint mode l capacity state entry) observed count packetOutside,
    helperFinish,StringDwordSequence.window mode (helpers mode l) l.start (helper_chain mode l)
    (Listing8DirectionBounds.helper_valid mode l capacity) state entry observed count helperOutside]

end SmcTuring.Appendix.Listing8DirectionTrace

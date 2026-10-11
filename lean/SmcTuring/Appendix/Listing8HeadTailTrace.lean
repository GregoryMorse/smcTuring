module
public import SmcTuring.Appendix.Listing8HeadTailFrames

public section
namespace SmcTuring.Appendix.Listing8HeadTailTrace
open Native Listing8DirectionLayout Listing8HeadTailBounds Listing8HeadTailFrames
@[expose] def xorFinish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  DwordXorSequence.finish mode (xorLayouts mode l) state
@[expose] def maskFinish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  let current := xorFinish mode l state
  {current with principal := DwordPackets.finish mode (masks mode l) current.principal}
@[expose] def finish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  let current := maskFinish mode l state
  {current with principal := DwordPackets.finish mode (heads mode l) current.principal}
@[expose] def program (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  DwordXorSequence.program mode (xorLayouts mode l) ++
    DwordPackets.program mode (masks mode l) (xorFinish mode l state).principal ++
    DwordPackets.program mode (heads mode l) (maskFinish mode l state).principal

theorem xor_endpoint (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l)) :
    (xorFinish mode l state).principal.pc = Arithmetic.encodeNat mode (maskPC mode l) := by
  simpa only [xorFinish,xor_span] using DwordXorSequence.endpoint mode (xorLayouts mode l)
    (selectionEnd mode l) (xor_chain mode l) (xor_valid mode l bounds) state entry

theorem mask_endpoint (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l)) :
    (maskFinish mode l state).principal.pc = Arithmetic.encodeNat mode (directionPC mode l) := by
  simpa only [maskFinish,mask_span] using DwordPackets.endpoint mode (masks mode l)
    (maskPC mode l) (masks_chain mode l)
    (fun site member => packets_valid mode l bounds site (List.mem_append_left _ member))
    (xorFinish mode l state).principal (xor_endpoint mode l bounds state entry)

theorem xor_current (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l))
    (headers : DwordPackets.Intact mode (masks mode l ++ heads mode l) state.principal.memory) :
    DwordPackets.Intact mode (masks mode l ++ heads mode l) (xorFinish mode l state).principal.memory := by
  intro reader member
  rw [DwordPackets.Current,xorFinish,DwordXorSequence.window mode (xorLayouts mode l) (selectionEnd mode l)
    (xor_chain mode l) (xor_valid mode l bounds) state entry reader.pc 6
    (fun writer writerMember => xor_headers mode l writer writerMember reader member)]
  exact headers reader member

theorem head_current (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l))
    (headers : DwordPackets.Intact mode (masks mode l ++ heads mode l) state.principal.memory) :
    DwordPackets.Intact mode (heads mode l) (maskFinish mode l state).principal.memory := by
  intro reader member
  rw [DwordPackets.Current,maskFinish,DwordPackets.window mode (masks mode l) (maskPC mode l) (masks_chain mode l)
    (fun site member => packets_valid mode l bounds site (List.mem_append_left _ member))
    (xorFinish mode l state).principal (xor_endpoint mode l bounds state entry) reader.pc 6
    (fun writer writerMember => mask_headers mode l writer writerMember reader member)]
  exact xor_current mode l bounds state entry headers reader (List.mem_append_right _ member)

/-- Only the complete initial XOR byte group and initial mask/head headers
are needed. Their actual intervening writes derive every later fetch. -/
theorem trace (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l))
    (xorImage : ByteMemory.bytesAt state.principal.memory (selectionEnd mode l)
      (DwordXorSequence.bytes mode (xorLayouts mode l)).length = DwordXorSequence.bytes mode (xorLayouts mode l))
    (headers : DwordPackets.Intact mode (masks mode l ++ heads mode l) state.principal.memory) :
    StringDword.Trace mode state (program mode l state) (finish mode l state) := by
  have first := DwordXorSequence.trace mode (xorLayouts mode l) (selectionEnd mode l) (xor_chain mode l)
    (xor_valid mode l bounds) (xor_frames mode l) state entry
    (DwordXorSequence.initial_helpers mode _ _ (xor_chain mode l) _ xorImage)
  have middle := DwordPackets.trace mode (masks mode l) (maskPC mode l) (masks_chain mode l)
    (fun site member => packets_valid mode l bounds site (List.mem_append_left _ member)) (masks_frames mode l)
    (xorFinish mode l state) (xor_endpoint mode l bounds state entry)
    (fun reader member => xor_current mode l bounds state entry headers reader (List.mem_append_left _ member))
  have last := DwordPackets.trace mode (heads mode l) (directionPC mode l) (heads_chain mode l)
    (fun site member => packets_valid mode l bounds site (List.mem_append_right _ member)) (heads_frames mode l bounds)
    (maskFinish mode l state) (mask_endpoint mode l bounds state entry) (head_current mode l bounds state entry headers)
  exact StringDword.trace_append mode (StringDword.trace_append mode first middle) last

theorem endpoint (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l)) :
    (finish mode l state).principal.pc = Arithmetic.encodeNat mode (endPC mode l) := by
  simpa only [finish,head_span] using DwordPackets.endpoint mode (heads mode l)
    (directionPC mode l) (heads_chain mode l)
    (fun site member => packets_valid mode l bounds site (List.mem_append_right _ member))
    (maskFinish mode l state).principal (mask_endpoint mode l bounds state entry)

theorem instruction_count (mode : Mode) (l : Layout) (state : StringExecution.State mode) :
    (program mode l state).length = if mode = .x86 then 5 else 10 := by
  rw [program,List.length_append,List.length_append,DwordXorSequence.instruction_count,
    DwordPackets.instruction_count,DwordPackets.instruction_count]
  cases mode <;> rfl

theorem registers (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l)) :
    (finish mode l state).principal.accumulator = DwordCode.lift mode (DwordCode.low mode state.principal.accumulator) ∧
    (finish mode l state).principal.stack = state.principal.stack ∧ (finish mode l state).principal.carry = false ∧
    (finish mode l state).sourceIndex = state.sourceIndex ∧ (finish mode l state).destinationIndex = state.destinationIndex ∧
    (finish mode l state).backwards = state.backwards := by
  have xorRegs := DwordXorSequence.registers mode (xorLayouts mode l) (selectionEnd mode l) (xor_chain mode l)
    (xor_valid mode l bounds) state entry
  have maskRegs := DwordPackets.registers mode (masks mode l) (xorFinish mode l state).principal
  have headRegs := DwordPackets.registers mode (heads mode l) (maskFinish mode l state).principal
  have nonempty : (xorLayouts mode l).length ≠ 0 := by cases mode <;> simp [xorLayouts]
  refine ⟨headRegs.1.trans (maskRegs.1.trans (by simpa only [xorFinish,ite_eq_right nonempty] using xorRegs.2.2.1)),
    headRegs.2.trans (maskRegs.2.trans xorRegs.1),?_,xorRegs.2.2.2.1,xorRegs.2.2.2.2.1,xorRegs.2.2.2.2.2⟩
  cases mode <;> rfl

theorem window (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode (selectionEnd mode l))
    (observed count : Nat)
    (xorOutside : ∀ writer ∈ xorLayouts mode l, writer.destination+4 ≤ observed ∨ observed+count ≤ writer.destination)
    (maskOutside : ∀ writer ∈ masks mode l, writer.target+4 ≤ observed ∨ observed+count ≤ writer.target)
    (headOutside : ∀ writer ∈ heads mode l, writer.target+4 ≤ observed ∨ observed+count ≤ writer.target) :
    ByteMemory.bytesAt (finish mode l state).principal.memory observed count = ByteMemory.bytesAt state.principal.memory observed count := by
  rw [finish,DwordPackets.window mode (heads mode l) (directionPC mode l) (heads_chain mode l)
    (fun site member => packets_valid mode l bounds site (List.mem_append_right _ member)) _
    (mask_endpoint mode l bounds state entry) observed count headOutside,
    maskFinish,DwordPackets.window mode (masks mode l) (maskPC mode l) (masks_chain mode l)
    (fun site member => packets_valid mode l bounds site (List.mem_append_left _ member)) _
    (xor_endpoint mode l bounds state entry) observed count maskOutside,xorFinish,
    DwordXorSequence.window mode (xorLayouts mode l) (selectionEnd mode l) (xor_chain mode l)
    (xor_valid mode l bounds) state entry observed count xorOutside]

end SmcTuring.Appendix.Listing8HeadTailTrace

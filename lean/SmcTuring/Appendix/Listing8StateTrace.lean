module
public import SmcTuring.Appendix.Listing8StateBounds

public section
namespace SmcTuring.Appendix.Listing8StateTrace
open Native Listing8StateLayout Listing8StateBounds
@[expose] def helperFinish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringDwordSequence.finish mode (helpers mode l) state
@[expose] def finish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  let current := helperFinish mode l state
  {current with principal := DwordPackets.finish mode (packets mode l) current.principal}
@[expose] def program (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringDwordSequence.program mode (helpers mode l) ++ DwordPackets.program mode (packets mode l) (helperFinish mode l state).principal

theorem helper_endpoint (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    (helperFinish mode l state).principal.pc = Arithmetic.encodeNat mode (newPC mode l) := by
  have last := StringDwordSequence.endpoint mode (helpers mode l) l.start (helper_chain mode l) (helper_valid mode l bounds) state entry
  rw [helper_length] at last
  exact last

theorem helper_headers (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start)
    (headers : DwordPackets.Intact mode (packets mode l) state.principal.memory) :
    DwordPackets.Intact mode (packets mode l) (helperFinish mode l state).principal.memory := by
  intro reader member
  rw [DwordPackets.Current,helperFinish,StringDwordSequence.window mode (helpers mode l) l.start (helper_chain mode l)
    (helper_valid mode l bounds) state entry reader.pc 6 (fun writer wm => helpers_outside_headers mode l writer wm reader member)]
  exact headers reader member

theorem trace (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start)
    (helperImage : ByteMemory.bytesAt state.principal.memory l.start (DwordMixedSequence.bytes mode (helpers mode l)).length =
      DwordMixedSequence.bytes mode (helpers mode l))
    (headers : DwordPackets.Intact mode (packets mode l) state.principal.memory) :
    StringDword.Trace mode state (program mode l state) (finish mode l state) := by
  have first := StringDwordSequence.trace mode (helpers mode l) l.start (helper_chain mode l) (helper_valid mode l bounds)
    (helper_frames mode l) state entry (DwordMixedSequence.intact_of_bytes mode _ _ (helper_chain mode l) _ helperImage)
  have last := DwordPackets.trace mode (packets mode l) (newPC mode l) (packet_chain mode l) (packet_valid mode l bounds)
    (packet_frames mode l bounds) (helperFinish mode l state) (helper_endpoint mode l bounds state entry)
    (helper_headers mode l bounds state entry headers)
  exact StringDword.trace_append mode first last

theorem endpoint (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    (finish mode l state).principal.pc = Arithmetic.encodeNat mode (endPC mode l) := by
  simpa only [finish,packet_span] using DwordPackets.endpoint mode (packets mode l) (newPC mode l)
    (packet_chain mode l) (packet_valid mode l bounds) (helperFinish mode l state).principal
    (helper_endpoint mode l bounds state entry)

theorem instruction_count (mode : Mode) (l : Layout) (state : StringExecution.State mode) :
    (program mode l state).length = if mode = .x86 then 6 else 12 := by
  rw [program,List.length_append,DwordPackets.instruction_count,packet_length]
  cases mode <;> rfl

theorem registers (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    (finish mode l state).principal.accumulator = DwordCode.lift mode (DwordCode.low mode state.principal.accumulator) ∧
    (finish mode l state).principal.stack = state.principal.stack ∧ (finish mode l state).principal.carry = false ∧
    (finish mode l state).sourceIndex = state.sourceIndex ∧ (finish mode l state).destinationIndex = state.destinationIndex ∧
    (finish mode l state).backwards = state.backwards := by
  have helper := StringDwordSequence.registers mode (helpers mode l) l.start (helper_chain mode l) (helper_valid mode l bounds) state entry
  have last := DwordPackets.registers mode (packets mode l) (helperFinish mode l state).principal
  have nonempty : (helpers mode l).length ≠ 0 := by rw [helper_length];cases mode <;> decide
  refine ⟨last.1.trans (by simpa only [helperFinish,ite_eq_right nonempty] using helper.2.2.1),last.2.trans helper.1,?_,rfl,rfl,rfl⟩
  cases mode <;> rfl

theorem window (mode : Mode) (l : Layout) (bounds : Bounds mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start)
    (observed count : Nat)
    (helperOutside : ∀ writer ∈ helpers mode l, writer.destination+4 ≤ observed ∨ observed+count ≤ writer.destination)
    (packetOutside : ∀ writer ∈ packets mode l, writer.target+4 ≤ observed ∨ observed+count ≤ writer.target) :
    ByteMemory.bytesAt (finish mode l state).principal.memory observed count = ByteMemory.bytesAt state.principal.memory observed count := by
  rw [finish,DwordPackets.window mode (packets mode l) (newPC mode l) (packet_chain mode l) (packet_valid mode l bounds) _
    (helper_endpoint mode l bounds state entry) observed count packetOutside,helperFinish,
    StringDwordSequence.window mode (helpers mode l) l.start (helper_chain mode l) (helper_valid mode l bounds) state entry observed count helperOutside]

end SmcTuring.Appendix.Listing8StateTrace

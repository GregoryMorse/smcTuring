module
public import SmcTuring.Native.StringMoveTrace
public import SmcTuring.Native.Relocation

public section
namespace SmcTuring.Native.StringTemplate
open StringExecution StringMoves

/-- Every complete subwindow of a snapshot store retains its bytes at the same
relative offset, including instruction headers and complete operand fields. -/
theorem copied_window (memory : ByteMemory.Memory) (source destination size offset count : Nat)
    (within : offset+count ≤ size) :
    ByteMemory.bytesAt (ByteMemory.putBytes memory destination (ByteMemory.bytesAt memory source size)) (destination+offset) count =
      ByteMemory.bytesAt memory (source+offset) count := by
  apply congrArg List.ofFn
  funext index
  have small := index.isLt
  have bound : offset+index.val < (ByteMemory.bytesAt memory source size).length := by
    rw [ByteMemory.bytes_at_length]; omega
  have written := ByteMemory.put_at_index memory destination (ByteMemory.bytesAt memory source size) ⟨offset+index.val,bound⟩
  simpa [ByteMemory.bytesAt,Nat.add_assoc] using written

/-- A copied packet is fetched by the same live decoder at its new position.
This proves retained decoding; location-sensitive operand meaning is addressed
by the explicit relocation laws below rather than silently identified. -/
theorem copied_fetch (mode : Mode) (widths : List Nat) (state : State mode) (forward : state.backwards = false)
    (sourceFits : state.sourceIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+widths.sum < 2^(8*mode.wordBytes))
    (separate : StringCopy.Apart state.sourceIndex.toNat state.destinationIndex.toNat widths.sum)
    (offset : Nat) (form : StringForm.Form mode) (legal : StringForm.Legal mode form)
    (within : offset+(StringForm.encode mode form).length ≤ widths.sum)
    (initialPacket : ByteMemory.bytesAt state.principal.memory (state.sourceIndex.toNat+offset)
      (StringForm.encode mode form).length = StringForm.encode mode form) :
    StringForm.fetch mode (run mode (forms mode widths) state).principal.memory (state.destinationIndex.toNat+offset) = some form := by
  apply StringForm.fetch_current_encoding mode _ _ form legal
  rw [effect mode widths state forward sourceFits destinationFits separate,copied_window _ _ _ _ _ _ within,initialPacket]

/-- Independent source/destination bases cover forward or backward placement. -/
theorem delta_internal (source destination nextOffset targetOffset : Nat) :
    Relocation.delta (source+nextOffset) (source+targetOffset) =
      Relocation.delta (destination+nextOffset) (destination+targetOffset) := by
  unfold Relocation.delta
  omega

theorem relative_internal (source destination nextOffset targetOffset : Nat) :
    Relocation.relative32 (source+nextOffset) (source+targetOffset) =
      Relocation.relative32 (destination+nextOffset) (destination+targetOffset) := by
  unfold Relocation.relative32
  rw [delta_internal source destination nextOffset targetOffset]

theorem signed_internal (source destination nextOffset targetOffset : Nat) :
    Relocation.SignedDelta (source+nextOffset) (source+targetOffset) ↔
      Relocation.SignedDelta (destination+nextOffset) (destination+targetOffset) := by
  unfold Relocation.SignedDelta
  rw [delta_internal source destination nextOffset targetOffset]

/-- RIP-relative fields whose referents move with the template keep exactly
those four displacement bytes. Absolute MOFFS pointers remain explicit fields
that must be initialized for their intended destination referent. -/
theorem rip_internal (source destination nextOffset targetOffset : Nat) :
    Relocation.memoryDisp .x64 (source+nextOffset) (source+targetOffset) =
      Relocation.memoryDisp .x64 (destination+nextOffset) (destination+targetOffset) :=
  relative_internal source destination nextOffset targetOffset

theorem rip_target (source destination nextOffset targetOffset : Nat)
    (fits : Relocation.SignedDelta (source+nextOffset) (source+targetOffset)) :
    Execution.memoryAddress .x64 (Arithmetic.encodeNat .x64 (destination+nextOffset))
      (Relocation.memoryDisp .x64 (source+nextOffset) (source+targetOffset)) =
        Arithmetic.encodeNat .x64 (destination+targetOffset) := by
  rw [rip_internal source destination nextOffset targetOffset]
  exact Relocation.memory_hits .x64 _ _ (fun _ => (signed_internal source destination nextOffset targetOffset).mp fits)

theorem absolute_external (next copiedNext target : Nat) :
    Relocation.memoryDisp .x86 next target = Relocation.memoryDisp .x86 copiedNext target := rfl

theorem absolute_target (copiedNext target : Nat) :
    Execution.memoryAddress .x86 (Arithmetic.encodeNat .x86 copiedNext)
      (Relocation.memoryDisp .x86 copiedNext target) = Arithmetic.encodeNat .x86 target := rfl

end SmcTuring.Native.StringTemplate

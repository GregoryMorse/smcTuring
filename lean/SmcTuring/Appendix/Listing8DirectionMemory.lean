module
public import SmcTuring.Appendix.Listing8DirectionTrace
public import SmcTuring.Native.DwordDataflow

public section
namespace SmcTuring.Appendix.Listing8DirectionMemory
open Native Listing8DirectionLayout
abbrev Dword := BitVec 32
@[expose] def blend (direction back forward : Dword) := ((~~~direction) &&& forward) ||| (direction &&& back)

/-- Exact memory result of the actually executed helper/Boolean prefix. -/
theorem memory (mode : Mode) (l : Layout) (capacity : endPC mode l < 2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    (Listing8DirectionTrace.finish mode l state).principal.memory =
      DwordDataflow.packetMemory (arithmetic mode l) (DwordDataflow.helperMemory (helpers mode l) state.principal.memory) := by
  rw [Listing8DirectionTrace.finish,DwordDataflow.packets mode _ _ (arithmetic_chain mode l)
    (Listing8DirectionBounds.arithmetic_valid mode l capacity) _
    (Listing8DirectionTrace.helper_endpoint mode l capacity state entry)]
  rw [Listing8DirectionTrace.helperFinish,DwordDataflow.helpers mode _ _ (helper_chain mode l)
    (Listing8DirectionBounds.helper_valid mode l capacity) state entry]

/-- The low head-XOR payload is the selected Boolean blend of the original
neighbor pointer halves; all reads arise from the executed writes. -/
theorem low_value (mode : Mode) (l : Layout) (capacity : endPC mode l < 2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    DwordCode.get (Listing8DirectionTrace.finish mode l state).principal.memory (directionPC mode l+6) =
      blend (DwordCode.get state.principal.memory (directionPC mode l+6))
        (DwordCode.get state.principal.memory (backPC mode l+6))
        (DwordCode.get state.principal.memory (forwardPC mode l+6)) := by
  rw [memory mode l capacity state entry]
  cases mode <;>
    simp [DwordDataflow.packetMemory,DwordDataflow.helperMemory,helpers,duplicate,copy,arithmetic,group,
      DwordPackets.raw,DwordArithmetic.result,blend,directionPC,maskPC,selectionEnd,combinedPC,
      forwardPC,notPC,backPC,copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,
      DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc,DwordCode.get_put,DwordDataflow.read_offset]

/-- The x64 high payload uses the original low direction mask because the
first printed helper duplicates that DWORD before either half is copied. -/
theorem high_value (l : Layout) (capacity : endPC .x64 l < 2^64)
    (state : StringExecution.State .x64) (entry : state.principal.pc = Arithmetic.encodeNat .x64 l.start) :
    DwordCode.get (Listing8DirectionTrace.finish .x64 l state).principal.memory (directionPC .x64 l+16) =
      blend (DwordCode.get state.principal.memory (directionPC .x64 l+6))
        (DwordCode.get state.principal.memory (backPC .x64 l+16))
        (DwordCode.get state.principal.memory (forwardPC .x64 l+16)) := by
  rw [memory .x64 l capacity state entry]
  simp [DwordDataflow.packetMemory,DwordDataflow.helperMemory,helpers,duplicate,copy,arithmetic,group,
    DwordPackets.raw,DwordArithmetic.result,blend,directionPC,maskPC,selectionEnd,combinedPC,
    forwardPC,notPC,backPC,copyStart,duplicateSpan,halves,Listing8PointerCopies.halfCount,
    DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc,DwordCode.get_put,DwordDataflow.read_offset]

theorem blend_mask (back forward : Dword) (takeBack : Bool) :
    blend (if takeBack then BitVec.allOnes 32 else 0) back forward = if takeBack then back else forward := by
  cases takeBack with
  | false =>
    change (BitVec.allOnes 32 &&& forward) ||| (0 &&& back) = forward
    rw [BitVec.allOnes_and]
    simp
  | true =>
    change (0 &&& forward) ||| (BitVec.allOnes 32 &&& back) = back
    rw [BitVec.allOnes_and]
    simp

end SmcTuring.Appendix.Listing8DirectionMemory

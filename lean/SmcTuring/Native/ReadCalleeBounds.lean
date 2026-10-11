module
public import SmcTuring.Native.ReaderBounds
public import SmcTuring.Native.CallsBounds
public import SmcTuring.Native.ReadCalleeImage

public section

namespace SmcTuring.Native.ReadCalleeBounds

open Execution MemoryRegion RegionExecution ReadCalleeImage

/-- The complete seven-instruction read/indirect-return footprint is derived
from the original pointer and StackTop plus static code/operand bounds. -/
theorem safe_run (mode : Mode) (region : Region) (start top slot : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top slot)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes)
    (code : region.Contains start (totalSize mode + 15))
    (topInside : region.Contains (Arithmetic.encodeNat mode top).toNat mode.wordBytes)
    (slotInside : region.Contains (Arithmetic.encodeNat mode slot).toNat mode.wordBytes)
    (pointer : region.Contains (load mode state.memory (ReaderImage.label mode start)).toNat mode.wordBytes) :
    SafeRun mode region (ReadCallee.program mode (params mode start top slot) state) state := by
  have readerCode : region.Contains start (ReaderImage.totalSize mode + 15) := by
    simpa only [Nat.add_zero] using WindowBounds.contained_slice region start (totalSize mode + 15) 0
      (ReaderImage.totalSize mode + 15) code (by cases mode <;> decide)
  have callCode : region.Contains (callStart mode start) (CallsImage.totalSize mode (.indirect slot) + 15) := by
    exact WindowBounds.contained_slice region start (totalSize mode + 15) (ReaderImage.totalSize mode)
      (CallsImage.totalSize mode (.indirect slot) + 15) code (by cases mode <;> simp [CallsImage.totalSize, CallsImage.resetSize, ReaderImage.totalSize, totalSize])
  have readSafe := ReaderBounds.safe_run mode region start state location (reader_fits mode start fits) readerCode pointer
  have topValue : load mode (ReadCallee.readEnd mode (params mode start top slot) state).memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes := by
    rw [read_memory mode start top slot state location]; exact value
  have callSafe := CallsBounds.safe_run mode region (callStart mode start) top slot (.indirect slot)
    (ReadCallee.readEnd mode (params mode start top slot) state) (read_pc mode start top slot state location)
    ranges (call_fits mode start slot fits) topValue callCode topInside slotInside slotInside
  exact WindowBounds.safe_run_append mode region _ _ state readSafe callSafe

theorem loaded (mode : Mode) (region : Region) (start top slot origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top slot)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode ≤ gridBase)
    (gap : origin + SpacedPacking.size mode whole ≤ gridBase - moffsOperandOffset mode)
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start top slot initial))
      (SpacedPacking.place mode origin whole))
    (intact : SpacedCombinedImage.Intact mode whole origin gridBase state.memory)
    (pointerOwned : SpacedCombinedImage.Owned mode whole origin gridBase (load mode state.memory (ReaderImage.label mode start)))
    (topOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode top))
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes)
    (code : region.Contains start (totalSize mode + 15))
    (topInside : region.Contains (Arithmetic.encodeNat mode top).toNat mode.wordBytes)
    (slotInside : region.Contains (Arithmetic.encodeNat mode slot).toNat mode.wordBytes)
    (pointer : region.Contains (load mode state.memory (ReaderImage.label mode start)).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state)
        (ReadCallee.program mode (params mode start top slot) state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (ReadCallee.finish mode (params mode start top slot) state) :=
  LoadedExecution.trace_complete mode region
    (ReadCalleeImage.trace mode start top slot origin gridBase initial whole state location ranges fits enough gap within intact pointerOwned topOwned)
    (safe_run mode region start top slot state location ranges fits value code topInside slotInside pointer)
    _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.ReadCalleeBounds

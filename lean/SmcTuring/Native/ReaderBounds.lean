module
public import SmcTuring.Native.WindowBounds
public import SmcTuring.Native.ReaderView
public import SmcTuring.Native.LoadedExecution

public section

namespace SmcTuring.Native.ReaderBounds

open Execution MemoryRegion RegionExecution ReaderImage

/-- The reader's entire mutable operand is inside its static code window. -/
theorem label_contained (mode : Mode) (region : Region) (start : Nat)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (code : region.Contains start (totalSize mode + 15)) :
    region.Contains (label mode start).toNat mode.wordBytes := by
  have small : start + labelOffset mode < 2 ^ (8 * mode.wordBytes) := by
    cases mode <;> simp only [labelOffset, totalSize, Mode.wordBytes] at * <;> omega
  rw [label, Arithmetic.encode_nat_toNat mode _ small]
  apply WindowBounds.contained_slice region start (totalSize mode + 15) (labelOffset mode) mode.wordBytes code
  cases mode <;> decide

private theorem code_window (mode : Mode) (region : Region) (start position : Nat)
    (code : region.Contains start (totalSize mode + 15))
    (lower : start ≤ position) (upper : position ≤ start + totalSize mode) :
    region.Contains position 15 := by
  have slice := WindowBounds.contained_slice region start (totalSize mode + 15) (position - start) 15 code (by omega)
  simpa only [Nat.add_sub_of_le lower] using slice

/-- All four live fetch/read/write footprints follow from the static reader
window and its original operand value. No future trace or safety premise is used.
The pointer may alias the reader label when its code-image contract allows it. -/
theorem safe_run (mode : Mode) (region : Region) (start : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (code : region.Contains start (totalSize mode + 15))
    (pointer : region.Contains (load mode state.memory (label mode start)).toNat mode.wordBytes) :
    SafeRun mode region
      [.memory .exchangeAcc (firstDisp mode start), Reader.storeForm mode (label mode start) (secondDisp mode),
        .exchangeIndirect, .moffs (load mode state.memory (label mode start))] state := by
  have positions := reached_positions mode start state location fits
  have firstHits := first_hits mode start state location
  have secondHits := second_hits mode start state location
  have labelInside := label_contained mode region start fits code
  have restoredPointer := Reader.restored_accumulator mode state (label mode start) (firstDisp mode start) (secondDisp mode) firstHits secondHits
  have firstSafe : Safe mode region (.memory .exchangeAcc (firstDisp mode start)) state := by
    apply WindowBounds.safe mode region
    · rw [positions.1]; exact code_window mode region start start code (by omega) (by omega)
    · change region.Contains (memoryAddress mode (nextPC mode (.memory .exchangeAcc (firstDisp mode start)) state) (firstDisp mode start)).toNat mode.wordBytes
      rw [firstHits]; exact labelInside
    · change region.Contains (memoryAddress mode (nextPC mode (.memory .exchangeAcc (firstDisp mode start)) state) (firstDisp mode start)).toNat mode.wordBytes
      rw [firstHits]; exact labelInside
  have secondSafe : Safe mode region (Reader.storeForm mode (label mode start) (secondDisp mode))
      (Reader.swapped mode state (firstDisp mode start)) := by
    apply WindowBounds.safe mode region
    · rw [positions.2.1]
      apply code_window mode region start _ code
      · simp only [secondEntry]; omega
      · cases mode <;> simp only [secondEntry, firstSize, totalSize] <;> omega
    · cases mode <;> trivial
    · have hits : Writes.address mode (Reader.storeForm mode (label mode start) (secondDisp mode))
          (Reader.swapped mode state (firstDisp mode start)) = label mode start := by
        cases mode with
        | x86 => rfl
        | x64 => exact secondHits
      rw [hits]; exact labelInside
  have thirdSafe : Safe mode region .exchangeIndirect
      (Reader.restored mode state (label mode start) (firstDisp mode start) (secondDisp mode)) := by
    apply WindowBounds.safe mode region
    · rw [positions.2.2.1]
      apply code_window mode region start _ code
      · simp only [thirdEntry]; omega
      · cases mode <;> simp only [thirdEntry, firstSize, secondSize, totalSize] <;> omega
    · change region.Contains (Reader.restored mode state (label mode start) (firstDisp mode start) (secondDisp mode)).accumulator.toNat mode.wordBytes
      rw [restoredPointer]; exact pointer
    · change region.Contains (Reader.restored mode state (label mode start) (firstDisp mode start) (secondDisp mode)).accumulator.toNat mode.wordBytes
      rw [restoredPointer]; exact pointer
  have fourthSafe : Safe mode region (.moffs (load mode state.memory (label mode start)))
      (Reader.dereferenced mode state (label mode start) (firstDisp mode start) (secondDisp mode)) := by
    apply WindowBounds.safe mode region
    · rw [positions.2.2.2]
      apply code_window mode region start _ code (by omega)
      cases mode <;> simp only [prefixSize, totalSize] <;> omega
    · trivial
    · exact pointer
  exact ⟨firstSafe, secondSafe, thirdSafe, fourthSafe, trivial⟩

/-- Literal constructed reader bytes execute inside a prescribed finite region.
The output agrees on every loaded byte and all four selected scalar components. -/
theorem loaded (mode : Mode) (region : Region) (start origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode ≤ gridBase)
    (gap : origin + SpacedPacking.size mode whole ≤ gridBase - moffsOperandOffset mode)
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start initial))
      (SpacedPacking.place mode origin whole))
    (intact : SpacedCombinedImage.Intact mode whole origin gridBase state.memory)
    (pointerOwned : SpacedCombinedImage.Owned mode whole origin gridBase (load mode state.memory (label mode start)))
    (code : region.Contains start (totalSize mode + 15))
    (pointer : region.Contains (load mode state.memory (label mode start)).toNat mode.wordBytes) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state)
        [.memory .exchangeAcc (firstDisp mode start), Reader.storeForm mode (label mode start) (secondDisp mode),
          .exchangeIndirect, .moffs (load mode state.memory (label mode start))] loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish)
        (Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)) :=
  LoadedExecution.trace_complete mode region
    (ReaderView.trace mode start origin gridBase initial whole state location fits enough gap within intact pointerOwned)
    (safe_run mode region start state location fits code pointer) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.ReaderBounds

module
public import SmcTuring.Native.WindowBounds
public import SmcTuring.Native.CallsImage
public import SmcTuring.Native.LoadedExecution

public section

namespace SmcTuring.Native.CallsBounds

open Execution MemoryRegion RegionExecution CallsImage

@[expose] def TargetWithin (mode : Mode) (region : Region) : Transfer → Prop
  | .relative _ => True
  | .indirect field => region.Contains (Arithmetic.encodeNat mode field).toNat mode.wordBytes

private theorem code_window (mode : Mode) (region : Region) (start : Nat) (transfer : Transfer) (position : Nat)
    (code : region.Contains start (totalSize mode transfer + 15))
    (lower : start ≤ position) (upper : position ≤ start + totalSize mode transfer) :
    region.Contains position 15 := by
  have slice := WindowBounds.contained_slice region start (totalSize mode transfer + 15) (position - start) 15 code (by omega)
  simpa only [Nat.add_sub_of_le lower] using slice

/-- Reset/CALL's complete access footprint is bounded from static code, the
initial StackTop value, and the actual return and indirect-target fields.
The indirect target is read before the distinct return-slot word is written. -/
theorem safe_run (mode : Mode) (region : Region) (start top slot : Nat) (transfer : Transfer) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top transfer)
    (fits : start + totalSize mode transfer < 2 ^ (8 * mode.wordBytes))
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes)
    (code : region.Contains start (totalSize mode transfer + 15))
    (topInside : region.Contains (Arithmetic.encodeNat mode top).toNat mode.wordBytes)
    (slotInside : region.Contains (Arithmetic.encodeNat mode slot).toNat mode.wordBytes)
    (targetInside : TargetWithin mode region transfer) :
    SafeRun mode region (Calls.program mode (firstDisp mode start top) (secondDisp mode start top) (callTarget mode start transfer)) state := by
  have positions := reached_positions mode start top transfer state location fits
  have resetReady := reset_ready mode start top transfer state location ranges
  have ready := stack_ready mode start top slot transfer state location ranges value
  have slotWritten := Calls.stack_slot mode state (Arithmetic.encodeNat mode top) (Arithmetic.encodeNat mode slot)
    (firstDisp mode start top) (secondDisp mode start top) ready
  have firstSafe : Safe mode region (.memory .exchangeStack (firstDisp mode start top)) state := by
    apply WindowBounds.safe mode region
    · rw [positions.1]; exact code_window mode region start transfer start code (by omega) (by omega)
    · change region.Contains (memoryAddress mode (nextPC mode (.memory .exchangeStack (firstDisp mode start top)) state) (firstDisp mode start top)).toNat mode.wordBytes
      rw [resetReady.firstHits]; exact topInside
    · change region.Contains (memoryAddress mode (nextPC mode (.memory .exchangeStack (firstDisp mode start top)) state) (firstDisp mode start top)).toNat mode.wordBytes
      rw [resetReady.firstHits]; exact topInside
  have secondSafe : Safe mode region (.memory .storeStack (secondDisp mode start top))
      (Calls.exchanged mode state (firstDisp mode start top)) := by
    apply WindowBounds.safe mode region
    · rw [positions.2.1]
      apply code_window mode region start transfer _ code
      · simp only [secondEntry]; omega
      · cases mode <;> cases transfer <;> simp only [secondEntry, oneSize, totalSize, resetSize] <;> omega
    · trivial
    · change region.Contains (memoryAddress mode
        (nextPC mode (.memory .storeStack (secondDisp mode start top)) (Calls.exchanged mode state (firstDisp mode start top)))
        (secondDisp mode start top)).toNat mode.wordBytes
      rw [resetReady.secondHits]; exact topInside
  have thirdSafe : Safe mode region ((callTarget mode start transfer).form mode)
      (Calls.reset mode state (firstDisp mode start top) (secondDisp mode start top)) := by
    apply WindowBounds.safe mode region
    · rw [positions.2.2]
      apply code_window mode region start transfer _ code
      · simp only [callEntry]; omega
      · cases transfer <;> simp only [callEntry, totalSize] <;> omega
    · cases transfer with
      | relative target => trivial
      | indirect field =>
        change region.Contains (memoryAddress mode
          (nextPC mode ((callTarget mode start (.indirect field)).form mode)
            (Calls.reset mode state (firstDisp mode start top) (secondDisp mode start top)))
          (Relocation.instructionDisp mode .callIndirect (start + resetSize mode) field)).toNat mode.wordBytes
        rw [indirect_hits mode start top field state location ranges]
        exact targetInside
    · have written : Writes.address mode ((callTarget mode start transfer).form mode)
          (Calls.reset mode state (firstDisp mode start top) (secondDisp mode start top)) = Arithmetic.encodeNat mode slot := by
        cases transfer <;> exact slotWritten
      rw [written]; exact slotInside
  exact ⟨firstSafe, secondSafe, thirdSafe, trivial⟩

/-- Literal placed reset/CALL bytes have a finite execution in the supplied
loaded region, with no assumed later trace or loaded evaluator result. -/
theorem loaded (mode : Mode) (region : Region) (start top slot origin gridBase : Nat) (transfer : Transfer)
    (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top transfer)
    (fits : start + totalSize mode transfer < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode ≤ gridBase)
    (gap : origin + SpacedPacking.size mode whole ≤ gridBase - moffsOperandOffset mode)
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start top transfer))
      (SpacedPacking.place mode origin whole))
    (intact : SpacedCombinedImage.Intact mode whole origin gridBase state.memory)
    (topOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode top))
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes)
    (code : region.Contains start (totalSize mode transfer + 15))
    (topInside : region.Contains (Arithmetic.encodeNat mode top).toNat mode.wordBytes)
    (slotInside : region.Contains (Arithmetic.encodeNat mode slot).toNat mode.wordBytes)
    (targetInside : TargetWithin mode region transfer) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state)
        (Calls.program mode (firstDisp mode start top) (secondDisp mode start top) (callTarget mode start transfer)) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish)
        (Calls.called mode state (firstDisp mode start top) (secondDisp mode start top) (callTarget mode start transfer)) :=
  LoadedExecution.trace_complete mode region
    (CallsImage.trace mode start top origin gridBase transfer whole state location ranges fits enough gap within intact topOwned)
    (safe_run mode region start top slot transfer state location ranges fits value code topInside slotInside targetInside)
    _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.CallsBounds

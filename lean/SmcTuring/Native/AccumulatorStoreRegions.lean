module
public import SmcTuring.Native.AccumulatorImage
public import SmcTuring.Native.WordCopyStoreRegions

public section
namespace SmcTuring.Native.AccumulatorStoreRegions

/-- The actual entry save stores exactly one complete save operand. -/
theorem prologue (mode : Mode) (allowed : Nat → Nat → Prop) (layout : AccumulatorLayout.Layout)
    (valid : AccumulatorLayout.Admissible mode layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.prologue) (save : allowed layout.save mode.wordBytes) :
    StringStoreRegions.Run mode allowed [StringWrites.liftNative mode (AccumulatorLayout.saveForm mode layout)] state := by
  have address:=AccumulatorImage.save_address mode layout valid state.principal entry
  have owned : Writes.OwnedRun mode (fun address => allowed address.toNat mode.wordBytes)
      [AccumulatorLayout.saveForm mode layout] state.principal := by
    constructor
    · rw [address]
      change allowed (Arithmetic.encodeNat mode layout.save).toNat mode.wordBytes
      rw [AccumulatorLayout.save_toNat mode layout valid]
      exact save
    · trivial
  exact StringStoreTemplateRuns.native mode allowed _ state owned

/-- All three epilogue stores use the actual pointer/save operand words. -/
theorem epilogue (mode : Mode) (allowed : Nat → Nat → Prop) (layout : AccumulatorLayout.Layout)
    (valid : AccumulatorLayout.Admissible mode layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.epilogue)
    (save : allowed layout.save mode.wordBytes) (pointer : allowed layout.pointer mode.wordBytes) :
    StringStoreRegions.Run mode allowed ((AccumulatorLayout.program mode layout).map (StringWrites.liftNative mode)) state := by
  have owned:=AccumulatorImage.supported_run mode layout valid state.principal entry
    (fun address => allowed address.toNat mode.wordBytes)
    (by rw [AccumulatorLayout.save_toNat mode layout valid];exact save)
    (by rw [AccumulatorLayout.pointer_toNat mode layout valid];exact pointer)
  exact StringStoreTemplateRuns.native mode allowed _ state owned

end SmcTuring.Native.AccumulatorStoreRegions

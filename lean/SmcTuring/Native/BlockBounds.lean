module
public import SmcTuring.Native.ImmediateBounds
public import SmcTuring.Native.LoadBounds
public import SmcTuring.Native.StoreBounds

public section

namespace SmcTuring.Native.BlockBounds

open Execution MemoryRegion RegionExecution BlockImage

/-- Static operand addresses of a block, excluding every computed heap pointer. -/
@[expose] def OperandsWithin (mode : Mode) (region : Region) : Block mode → Prop
  | .immediate layout => region.Contains (Arithmetic.encodeNat mode layout.constant).toNat mode.wordBytes
  | .load layout => SourceAccess.GuardFields mode region layout.address.offset.guard ∧
      region.Contains (Arithmetic.encodeNat mode (AddressImage.pointerPosition mode layout.address)).toNat mode.wordBytes
  | .store layout => SourceAccess.GuardFields mode region layout.address.offset.guard ∧
      region.Contains (Arithmetic.encodeNat mode (AddressImage.pointerPosition mode layout.address)).toNat mode.wordBytes

/-- Static placement and full-word geometry. No executed state, future pointer,
Ready predicate or safe trace is stored in this certificate. -/
structure StaticBounds (mode : Mode) (region : Region) (block : Block mode) : Prop where
  code : PlacedBounds.ControlWithin mode region (context mode block).origin (context mode block).whole
  data : SourceAccess.DataWithin mode region (context mode block).gridBase (context mode block).cells
  top : region.Contains (Arithmetic.encodeNat mode (context mode block).top).toNat mode.wordBytes
  slot : region.Contains (Arithmetic.encodeNat mode (context mode block).slot).toNat mode.wordBytes
  operands : OperandsWithin mode region block

/-- All three literal source forms have bounded actual accesses from static
geometry, current readiness/representation and the source cell bounds. -/
theorem safe_run (mode : Mode) (region : Region) (block : Block mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode block state) (bounds : Bounds mode block source) (rep : Rep mode block source state)
    (static : StaticBounds mode region block) :
    SafeRun mode region (program mode block source state) state := by
  cases block with
  | immediate layout => exact ImmediateBounds.safe_run mode region layout state ready static.code static.data static.top static.slot static.operands
  | load layout => exact LoadBounds.safe_run mode region layout source state ready bounds rep static.code static.operands.1 static.data static.operands.2
  | store layout => exact StoreBounds.safe_run mode region layout source state ready bounds rep static.code static.operands.1 static.data static.operands.2

theorem loaded (mode : Mode) (region : Region) (block : Block mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode block state) (bounds : Bounds mode block source) (rep : Rep mode block source state)
    (static : StaticBounds mode region block) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (program mode block source state) loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (finish mode block source state) :=
  LoadedExecution.trace_complete mode region (BlockImage.correct mode block source state ready bounds rep).trace
    (safe_run mode region block source state ready bounds rep static) _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.BlockBounds

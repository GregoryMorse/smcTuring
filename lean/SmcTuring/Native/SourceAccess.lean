module
public import SmcTuring.Native.GuardInvocationBounds
public import SmcTuring.Native.BlockImage

public section

namespace SmcTuring.Native.SourceAccess

open Execution MemoryRegion RegionExecution

/-- Static full-word metadata intervals shared by source guards. No current
contents, executed states or future access certificate occur in this record. -/
structure GuardFields (mode : Mode) (region : Region) (guard : GuardImage.Layout mode) : Prop where
  top : region.Contains (Arithmetic.encodeNat mode guard.setup.top).toNat mode.wordBytes
  slot : region.Contains (Arithmetic.encodeNat mode guard.setup.slot).toNat mode.wordBytes
  resume : region.Contains (Arithmetic.encodeNat mode guard.setup.resume).toNat mode.wordBytes
  scratch : region.Contains (Arithmetic.encodeNat mode guard.setup.scratch).toNat mode.wordBytes
  candidate : region.Contains (Arithmetic.encodeNat mode guard.setup.candidate).toNat mode.wordBytes
  boundary : region.Contains (Arithmetic.encodeNat mode guard.setup.boundary).toNat mode.wordBytes
  zero : region.Contains (Arithmetic.encodeNat mode guard.zero).toNat mode.wordBytes
  mask : region.Contains (Arithmetic.encodeNat mode guard.mask).toNat mode.wordBytes
  selected : region.Contains (Arithmetic.encodeNat mode guard.selected).toNat mode.wordBytes
  terminal : region.Contains (Arithmetic.encodeNat mode guard.terminal).toNat mode.wordBytes

/-- Complete represented finite source words, independent of their values. -/
structure DataWithin (mode : Mode) (region : Region) (gridBase cells : Nat) : Prop where
  registers : ∀ register, region.Contains (SourceData.registerWord mode gridBase register).toNat mode.wordBytes
  heap : ∀ position : Nat × Bool, position.1 < cells → region.Contains (SourceData.heapWord mode gridBase position).toNat mode.wordBytes

theorem guard_safe (mode : Mode) (region : Region) (layout : GuardImage.Layout mode) (state : State mode)
    (ready : GuardImage.Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.setup.origin layout.setup.whole)
    (fields : GuardFields mode region layout) :
    SafeRun mode region (GuardImage.program mode layout state) state :=
  GuardBounds.safe_run mode region layout state ready code fields.top fields.slot fields.resume fields.scratch
    fields.candidate fields.boundary fields.zero fields.mask fields.selected fields.terminal

theorem invocation_safe (mode : Mode) (region : Region) (layout : GuardInvocationImage.Layout mode) (state : State mode)
    (ready : GuardInvocationImage.Ready mode layout state) (code : PlacedBounds.ControlWithin mode region layout.guard.setup.origin layout.guard.setup.whole)
    (fields : GuardFields mode region layout.guard) :
    SafeRun mode region (GuardInvocationImage.program mode layout state) state :=
  GuardInvocationBounds.safe_run mode region layout state ready code fields.top fields.slot fields.resume fields.scratch
    fields.candidate fields.boundary fields.zero fields.mask fields.selected fields.terminal

end SmcTuring.Native.SourceAccess

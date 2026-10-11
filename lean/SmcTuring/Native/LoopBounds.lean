module
public import SmcTuring.Native.ProgramBounds
public import SmcTuring.Native.LoopImage

public section

namespace SmcTuring.Native.LoopBounds

open Execution MemoryRegion RegionExecution BlockImage ProgramImage

/-- Static code and operand geometry for every source pass and its backedge.
No execution state, later Ready or access trace occurs in this certificate. -/
structure Static (mode : Mode) (region : Region) (ctx : Context mode)
    (schedule : List (Block mode)) (layout : LoopImage.Layout) : Prop where
  blocks : ∀ block, block ∈ schedule → BlockBounds.StaticBounds mode region block
  code : PlacedBounds.ControlWithin mode region ctx.origin ctx.whole
  top : region.Contains (Arithmetic.encodeNat mode ctx.top).toNat mode.wordBytes
  slot : region.Contains (Arithmetic.encodeNat mode ctx.slot).toNat mode.wordBytes
  target : region.Contains (Arithmetic.encodeNat mode layout.target).toNat mode.wordBytes

/-- Original setup plus the current preserved invariant derives all accesses
of the actual accepted body/backedge, without resetting the byte memory. -/
theorem pass_safe (mode : Mode) (region : Region) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode → Prop) (pointer : Nat)
    (sourceSetup : Setup mode ctx schedule initial frozen pointer)
    (blocks : List (Block mode)) (included : ∀ block, block ∈ blocks → block ∈ schedule)
    (layout : LoopImage.Layout)
    (loopSetup : LoopImage.Setup mode ctx layout initial frozen pointer (entry mode blocks (Arithmetic.encodeNat mode layout.start)))
    (geometry : Static mode region ctx schedule layout)
    (source : Dolan.Mov.State) (state : State mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = entry mode blocks (Arithmetic.encodeNat mode layout.start))
    (linked : Linked mode blocks (Arithmetic.encodeNat mode layout.start)) (bounds : Bounded mode blocks source)
    (accepted : (run mode blocks source state).accepted = true) :
    let body := run mode blocks source state
    SafeRun mode region (body.forms ++ LoopImage.program mode ctx layout) state := by
  have checked := ProgramImage.correct mode ctx schedule initial frozen pointer sourceSetup blocks included source state _ inv location linked bounds
  have boundary := successful_boundary mode ctx schedule initial frozen pointer sourceSetup blocks included source state _ inv location linked bounds accepted
  have topValue := (boundary.2.frames _ loopSetup.topFrozen).trans loopSetup.topValue
  have backedge := PlacedBounds.calls_safe mode region _ _ _ _ _ _ _ boundary.1
    loopSetup.ranges loopSetup.fits topValue loopSetup.within geometry.code geometry.top geometry.slot geometry.target
  exact PlacedBounds.safe_trace_append mode region checked.trace
    (ProgramBounds.safe_run mode region ctx schedule initial frozen pointer sourceSetup geometry.blocks blocks included source state _ inv location linked bounds) backedge

end SmcTuring.Native.LoopBounds

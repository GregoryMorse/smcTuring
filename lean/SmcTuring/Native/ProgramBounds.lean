module
public import SmcTuring.Native.BlockBounds
public import SmcTuring.Native.ProgramImage

public section

namespace SmcTuring.Native.ProgramBounds

open Execution MemoryRegion RegionExecution BlockImage ProgramImage

/-- A complete source schedule's access safety follows by the actual invariant
and source cell bounds. Current block readiness is derived at every boundary;
only static geometry is supplied for the schedule, not future safe executions. -/
theorem safe_run (mode : Mode) (region : Region) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode → Prop) (pointer : Nat)
    (setup : Setup mode ctx schedule initial frozen pointer)
    (static : ∀ block, block ∈ schedule → BlockBounds.StaticBounds mode region block)
    (blocks : List (Block mode)) (included : ∀ block, block ∈ blocks → block ∈ schedule)
    (source : Dolan.Mov.State) (state : State mode) (endPC : Word mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = entry mode blocks endPC) (linked : Linked mode blocks endPC)
    (bounds : Bounded mode blocks source) :
    SafeRun mode region (run mode blocks source state).forms state := by
  induction blocks generalizing source state with
  | nil => trivial
  | cons block rest ih =>
    have member := included block (by simp)
    have ready := block_ready mode ctx schedule initial frozen pointer setup block member source state inv location
    have common := setup.common block member
    have rep : Rep mode block source state := by simpa only [Rep, common, represented] using inv.represented
    have first := BlockBounds.safe_run mode region block source state ready bounds.1 rep (static block member)
    cases accepted : accepts block source with
    | false => simpa only [run, accepted, Bool.false_eq_true, ite_false] using first
    | true =>
      have middleInv := block_invariant mode ctx schedule initial frozen pointer setup block member source state inv location bounds.1 accepted
      have checked := BlockImage.correct mode block source state ready bounds.1 rep
      have nextPC : (BlockImage.finish mode block source state).pc = entry mode rest endPC := by
        simpa only [accepted, Bool.true_eq, ite_true, linked.1] using checked.pc
      have later := ih (fun next nextMember => included next (by simp [nextMember]))
        (result block source) (BlockImage.finish mode block source state) middleInv nextPC linked.2 (bounds.2 accepted)
      simpa only [run, accepted, Bool.true_eq, ite_true] using PlacedBounds.safe_trace_append mode region checked.trace first later

theorem loaded (mode : Mode) (region : Region) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode → Prop) (pointer : Nat)
    (setup : Setup mode ctx schedule initial frozen pointer)
    (static : ∀ block, block ∈ schedule → BlockBounds.StaticBounds mode region block)
    (blocks : List (Block mode)) (included : ∀ block, block ∈ blocks → block ∈ schedule)
    (source : Dolan.Mov.State) (state : State mode) (endPC : Word mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = entry mode blocks endPC) (linked : Linked mode blocks endPC)
    (bounds : Bounded mode blocks source) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode region (LoadedExecution.snapshot mode region state) (run mode blocks source state).forms loadedFinish ∧
      StateAgree mode region (LoadedExecution.expand mode region loadedFinish) (run mode blocks source state).native :=
  LoadedExecution.trace_complete mode region
    (ProgramImage.correct mode ctx schedule initial frozen pointer setup blocks included source state endPC inv location linked bounds).trace
    (safe_run mode region ctx schedule initial frozen pointer setup static blocks included source state endPC inv location linked bounds)
    _ (LoadedExecution.snapshot_agrees mode region state)

end SmcTuring.Native.ProgramBounds

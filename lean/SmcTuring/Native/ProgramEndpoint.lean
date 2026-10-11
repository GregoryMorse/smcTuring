module
public import SmcTuring.Native.ProgramImage

public section

namespace SmcTuring.Native.ProgramEndpoint

open Execution BlockImage ProgramImage

/-- Original terminal-field values and their membership in the immutable set.
This static record contains no later state or execution conclusion. -/
@[expose] def FailureSnapshot (mode : Mode) (initial : State mode) (frozen : Word mode → Prop)
    (target : Word mode) : Block mode → Prop
  | .immediate _ => True
  | .load layout => frozen (Arithmetic.encodeNat mode layout.address.offset.guard.terminal) ∧
      load mode initial.memory (Arithmetic.encodeNat mode layout.address.offset.guard.terminal) = target
  | .store layout => frozen (Arithmetic.encodeNat mode layout.address.offset.guard.terminal) ∧
      load mode initial.memory (Arithmetic.encodeNat mode layout.address.offset.guard.terminal) = target

theorem failure_target (mode : Mode) (block : Block mode) (source : Dolan.Mov.State)
    (initial state : State mode) (frozen : Word mode → Prop) (target : Word mode)
    (snapshot : FailureSnapshot mode initial frozen target block)
    (preserved : frames mode frozen initial state) (rejected : accepts block source = false) :
    failureTarget mode block state = target := by
  cases block with
  | immediate layout =>
    simp only [accepts, instruction, Dolan.Mov.execute, Option.isSome_some] at rejected
    cases rejected
  | load layout => exact (preserved _ snapshot.1).trans snapshot.2
  | store layout => exact (preserved _ snapshot.1).trans snapshot.2

/-- Derive the endpoint from literal block effects and the maintained invariant.
Rejected paths use the original frozen terminal field; successful paths use Linked. -/
theorem endpoint (mode : Mode) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode → Prop) (pointer : Nat)
    (setup : Setup mode ctx schedule initial frozen pointer) (target : Word mode)
    (snapshots : ∀ block, block ∈ schedule → FailureSnapshot mode initial frozen target block)
    (blocks : List (Block mode)) (included : ∀ block, block ∈ blocks → block ∈ schedule)
    (source : Dolan.Mov.State) (state : State mode) (endPC : Word mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = entry mode blocks endPC) (linked : Linked mode blocks endPC)
    (bounds : Bounded mode blocks source) :
    (run mode blocks source state).native.pc = if (run mode blocks source state).accepted then endPC else target := by
  induction blocks generalizing source state with
  | nil => exact location
  | cons block rest ih =>
    have member := included block (by simp)
    have ready := block_ready mode ctx schedule initial frozen pointer setup block member source state inv location
    have common := setup.common block member
    have rep : Rep mode block source state := by simpa only [Rep, common, represented] using inv.represented
    have checked := BlockImage.correct mode block source state ready bounds.1 rep
    cases accepted : accepts block source with
    | false =>
      have final := failure_target mode block source initial state frozen target (snapshots block member) inv.frames accepted
      simpa only [run, accepted, Bool.false_eq_true, ite_false, final] using checked.pc
    | true =>
      have middleInv := block_invariant mode ctx schedule initial frozen pointer setup block member source state inv location bounds.1 accepted
      have nextPC : (BlockImage.finish mode block source state).pc = entry mode rest endPC := by
        simpa only [accepted, Bool.true_eq, ite_true, linked.1] using checked.pc
      have later := ih (fun next nextMember => included next (by simp [nextMember]))
        (result block source) (BlockImage.finish mode block source state) middleInv nextPC linked.2 (bounds.2 accepted)
      simpa only [run, accepted, Bool.true_eq, ite_true] using later

end SmcTuring.Native.ProgramEndpoint

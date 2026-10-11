module
public import SmcTuring.Native.LoopBounds
public import SmcTuring.Native.ProgramEndpoint
public import SmcTuring.Native.ControlBounds

public section

namespace SmcTuring.Native.ProgramIteration

open Execution MemoryRegion RegionExecution BlockImage ProgramImage

/-- Literal bounded source iteration. An undefined pass stops the computation. -/
@[expose] def sourceRun (program : List Dolan.Mov.Instruction) : Nat → Dolan.Mov.State → Option Dolan.Mov.State
  | 0, source => some source
  | count + 1, source => (Dolan.Mov.run program source).bind (sourceRun program count)

/-- Each accepted pass feeds its actual resulting source and byte state into the
next pass. No initializer or fresh image is invoked in this recursion. -/
@[expose] def run (mode : Mode) (ctx : Context mode) (blocks : List (Block mode)) (layout : LoopImage.Layout) :
    Nat → Dolan.Mov.State → State mode → Outcome mode
  | 0, source, state => ⟨source, state, [], true⟩
  | count + 1, source, state =>
      let body := ProgramImage.run mode blocks source state
      if body.accepted then
        let next := LoopImage.finish mode ctx layout body.native
        let later := run mode ctx blocks layout count body.source next
        { later with forms := (body.forms ++ LoopImage.program mode ctx layout) ++ later.forms }
      else body

/-- Bounds depend only on literal source execution, not on a later native state,
trace, Ready or target. Allocation capacity remains fixed for the whole path. -/
@[expose] def Bounded (mode : Mode) (blocks : List (Block mode)) : Nat → Dolan.Mov.State → Prop
  | 0, _ => True
  | count + 1, source => ProgramImage.Bounded mode blocks source ∧
      match Dolan.Mov.run (blocks.map instruction) source with
      | none => True
      | some next => Bounded mode blocks count next

structure Spec (mode : Mode) (region : Region) (ctx : Context mode) (blocks : List (Block mode))
    (layout : LoopImage.Layout) (initial : State mode) (frozen : Word mode → Prop) (pointer : Nat)
    (terminal : Word mode) (count : Nat) (source : Dolan.Mov.State) (state : State mode) (outcome : Outcome mode) : Prop where
  sourceRun : sourceRun (blocks.map instruction) count source = if outcome.accepted then some outcome.source else none
  represented : represented mode ctx outcome.source outcome.native
  trace : Fetch.Trace mode state outcome.forms outcome.native
  owned : Writes.OwnedRun mode (ProgramImage.owned mode ctx) outcome.forms state
  safe : SafeRun mode region outcome.forms state
  boundary : outcome.accepted = true → Invariant mode ctx initial frozen pointer outcome.source outcome.native
  pc : outcome.native.pc = if outcome.accepted then entry mode blocks (Arithmetic.encodeNat mode layout.start) else terminal

/-- Induction composes actual consecutive byte executions. The original snapshot
stays fixed, while each next Ready and access fact follows from the preceding
body/backedge invariant. Rejected passes stop without executing their backedge. -/
theorem correct (mode : Mode) (region : Region) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode → Prop) (pointer : Nat)
    (setup : Setup mode ctx schedule initial frozen pointer) (terminal : Word mode)
    (snapshots : ∀ block, block ∈ schedule → ProgramEndpoint.FailureSnapshot mode initial frozen terminal block)
    (blocks : List (Block mode)) (included : ∀ block, block ∈ blocks → block ∈ schedule)
    (layout : LoopImage.Layout)
    (loopSetup : LoopImage.Setup mode ctx layout initial frozen pointer (entry mode blocks (Arithmetic.encodeNat mode layout.start)))
    (geometry : LoopBounds.Static mode region ctx schedule layout)
    (count : Nat) (source : Dolan.Mov.State) (state : State mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = entry mode blocks (Arithmetic.encodeNat mode layout.start))
    (linked : Linked mode blocks (Arithmetic.encodeNat mode layout.start)) (bounds : Bounded mode blocks count source) :
    Spec mode region ctx blocks layout initial frozen pointer terminal count source state (run mode ctx blocks layout count source state) := by
  induction count generalizing source state with
  | zero => exact ⟨rfl, inv.represented, .nil state, trivial, trivial, fun _ => inv, location⟩
  | succ count ih =>
    have body := ProgramImage.correct mode ctx schedule initial frozen pointer setup blocks included source state _ inv location linked bounds.1
    cases accepted : (ProgramImage.run mode blocks source state).accepted with
    | false =>
      have stopped : Dolan.Mov.run (blocks.map instruction) source = none := by simpa only [accepted, Bool.false_eq_true, ite_false] using body.sourceRun
      have endpoint := ProgramEndpoint.endpoint mode ctx schedule initial frozen pointer setup terminal snapshots blocks included source state _ inv location linked bounds.1
      refine { sourceRun := ?_, represented := ?_, trace := ?_, owned := ?_, safe := ?_, boundary := ?_, pc := ?_ }
      · simp only [run, accepted, Bool.false_eq_true, ite_false, sourceRun, stopped, Option.bind_none]
      · simpa only [run, accepted, Bool.false_eq_true, ite_false] using body.represented
      · simpa only [run, accepted, Bool.false_eq_true, ite_false] using body.trace
      · simpa only [run, accepted, Bool.false_eq_true, ite_false] using body.owned
      · simpa only [run, accepted, Bool.false_eq_true, ite_false] using
          ProgramBounds.safe_run mode region ctx schedule initial frozen pointer setup geometry.blocks blocks included source state _ inv location linked bounds.1
      · simp only [run, accepted, Bool.false_eq_true, ite_false, false_implies]
      · simpa only [run, accepted, Bool.false_eq_true, ite_false] using endpoint
    | true =>
      have pass := LoopImage.pass_correct mode ctx schedule initial frozen pointer setup blocks included layout loopSetup source state inv location linked bounds.1 accepted
      have passSafe := LoopBounds.pass_safe mode region ctx schedule initial frozen pointer setup blocks included layout loopSetup geometry source state inv location linked bounds.1 accepted
      have laterBounds : Bounded mode blocks count (ProgramImage.run mode blocks source state).source := by
        simpa only [pass.1] using bounds.2
      have later := ih (ProgramImage.run mode blocks source state).source
        (LoopImage.finish mode ctx layout (ProgramImage.run mode blocks source state).native) pass.2.2.2.1 pass.2.2.2.2 laterBounds
      have allOwned : Writes.OwnedRun mode (ProgramImage.owned mode ctx)
          (((ProgramImage.run mode blocks source state).forms ++ LoopImage.program mode ctx layout) ++
            (run mode ctx blocks layout count (ProgramImage.run mode blocks source state).source
              (LoopImage.finish mode ctx layout (ProgramImage.run mode blocks source state).native)).forms) state := by
        rw [Writes.owned_run_append, ←Fetch.trace_run_eq mode pass.2.1]
        exact ⟨pass.2.2.1, later.owned⟩
      have allSafe := PlacedBounds.safe_trace_append mode region pass.2.1 passSafe later.safe
      refine { sourceRun := ?_, represented := ?_, trace := ?_, owned := ?_, safe := ?_, boundary := ?_, pc := ?_ }
      · simpa only [run, accepted, Bool.true_eq, ite_true, sourceRun, pass.1, Option.bind_some] using later.sourceRun
      · simpa only [run, accepted, Bool.true_eq, ite_true] using later.represented
      · simpa only [run, accepted, Bool.true_eq, ite_true] using Fetch.trace_append mode pass.2.1 later.trace
      · simpa only [run, accepted, Bool.true_eq, ite_true] using allOwned
      · simpa only [run, accepted, Bool.true_eq, ite_true] using allSafe
      · simpa only [run, accepted, Bool.true_eq, ite_true] using later.boundary
      · simpa only [run, accepted, Bool.true_eq, ite_true] using later.pc

/-- Every accepted source pass contributes its three actual backedge events.
This rules out zero-progress native iterations, independently of body length. -/
theorem accepted_length (mode : Mode) (ctx : Context mode) (blocks : List (Block mode)) (layout : LoopImage.Layout)
    (count : Nat) (source : Dolan.Mov.State) (state : State mode)
    (accepted : (run mode ctx blocks layout count source state).accepted = true) :
    3 * count ≤ (run mode ctx blocks layout count source state).forms.length := by
  induction count generalizing source state with
  | zero => simp only [Nat.mul_zero]; exact Nat.zero_le _
  | succ count ih =>
    cases branch : (ProgramImage.run mode blocks source state).accepted with
    | false => simp only [run, branch, Bool.false_eq_true, ite_false] at accepted
    | true =>
      have laterAccepted : (run mode ctx blocks layout count (ProgramImage.run mode blocks source state).source
          (LoopImage.finish mode ctx layout (ProgramImage.run mode blocks source state).native)).accepted = true := by
        simpa only [run, branch, Bool.true_eq, ite_true] using accepted
      have later := ih _ _ laterAccepted
      simp only [run, branch, ite_true, List.length_append, LoopImage.program, Calls.program,
        List.length_cons, List.length_nil, Nat.mul_succ]
      omega

theorem targets (mode : Mode) (region : Region) (ctx : Context mode) (blocks : List (Block mode))
    (layout : LoopImage.Layout) (initial : State mode) (frozen : Word mode → Prop) (pointer : Nat)
    (terminal : Word mode) (count : Nat) (source : Dolan.Mov.State) (state : State mode) (outcome : Outcome mode)
    (spec : Spec mode region ctx blocks layout initial frozen pointer terminal count source state outcome)
    (environment : MappedExecution.Environment) (mapping : MappedExecution.Mapped mode environment region)
    (entryValid : AddressSpace.Valid mode environment.paging (entry mode blocks (Arithmetic.encodeNat mode layout.start)).toNat)
    (terminalValid : AddressSpace.Valid mode environment.paging terminal.toNat) :
    ControlBounds.Targets mode environment outcome.forms state := by
  apply ControlBounds.targets_of_trace mode environment region mapping spec.trace spec.safe
  rw [spec.pc]
  split
  · exact entryValid
  · exact terminalValid

end SmcTuring.Native.ProgramIteration

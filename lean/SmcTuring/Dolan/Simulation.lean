module
public import SmcTuring.Dolan.Progress

public section

namespace SmcTuring.Dolan.Mov

open Encoding Table

@[expose] def repeatRun (program : List Instruction) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (run program s).bind (repeatRun program n)

theorem passes_iff_repeat (program : List Instruction) (n : Nat) (s finish : State) :
    Passes program s finish n ↔ repeatRun program n s = some finish := by
  induction n generalizing s finish with
  | zero =>
    constructor
    · intro completed
      cases completed
      rfl
    · intro completed
      have equal : s = finish := Option.some.inj completed
      subst finish
      exact Passes.zero s
  | succ n ih =>
    constructor
    · intro completed
      cases completed with
      | succ first rest => simpa [repeatRun, first] using (ih _ _).1 rest
    · intro completed
      cases first : run program s with
      | none => simp [repeatRun, first] at completed
      | some middle =>
        have rest : repeatRun program n middle = some finish := by simpa [repeatRun, first] using completed
        exact Passes.succ first ((ih _ _).2 rest)

theorem repeat_add (program : List Instruction) (first second : Nat) (s : State) :
    repeatRun program (first + second) s = (repeatRun program first s).bind (repeatRun program second) := by
  induction first generalizing s with
  | zero => simp [repeatRun]
  | succ first ih =>
    rw [Nat.succ_add]
    simp only [repeatRun]
    cases run program s <;> simp [ih]

@[expose] def LoopHalts (program : List Instruction) (s : State) : Prop :=
  ∃ n finish, Passes program s finish n ∧ run program finish = none

@[expose] def LoopDiverges (program : List Instruction) (s : State) : Prop :=
  ∀ n, ∃ finish, Passes program s finish n

theorem loop_failure_halts (program : List Instruction) (n : Nat) (s : State)
    (failed : repeatRun program n s = none) : LoopHalts program s := by
  induction n generalizing s with
  | zero => simp [repeatRun] at failed
  | succ n ih =>
    cases first : run program s with
    | none => exact ⟨0, s, Passes.zero s, first⟩
    | some middle =>
      have rest : repeatRun program n middle = none := by simpa [repeatRun, first] using failed
      rcases ih middle rest with ⟨k, finish, completed, fault⟩
      exact ⟨k + 1, finish, Passes.succ first completed, fault⟩

theorem loop_diverges_iff_not_halts (program : List Instruction) (s : State) :
    LoopDiverges program s ↔ ¬ LoopHalts program s := by
  constructor
  · intro infinite halted
    rcases halted with ⟨n, finish, completed, fault⟩
    have history := (passes_iff_repeat program n s finish).1 completed
    rcases infinite (n + 1) with ⟨later, laterPasses⟩
    have laterRun := (passes_iff_repeat program (n + 1) s later).1 laterPasses
    rw [repeat_add, history] at laterRun
    simp [repeatRun, fault] at laterRun
  · intro notHalted n
    cases h : repeatRun program n s with
    | none => exact False.elim (notHalted (loop_failure_halts program n s h))
    | some finish => exact ⟨finish, (passes_iff_repeat program n s finish).2 h⟩

/-- Each finite TM execution is matched by a finite number of passes of the
same static MOV body. The resulting configuration includes the complete tape. -/
theorem simulate_run {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (n : Nat) (c next : TM.Configuration alphabet states) (s : State)
    (rep : ScanRep machine c 0 s) (completed : TM.run machine n c = some next) :
    ∃ k finish, Passes kernelProgram s finish k ∧ ScanRep machine next 0 finish := by
  induction n generalizing c next s with
  | zero =>
    have equal : c = next := Option.some.inj completed
    subst next
    exact ⟨0, s, Passes.zero s, rep⟩
  | succ n ih =>
    cases first : TM.step machine c with
    | none => simp [TM.run, first] at completed
    | some middle =>
      have rest : TM.run machine n middle = some next := by simpa [TM.run, first] using completed
      rcases simulate_step machine c middle 0 s rep first with ⟨k, physical, _, _, firstPasses, nextRep⟩
      rcases ih middle next physical nextRep rest with ⟨l, finish, restPasses, represented⟩
      exact ⟨k + l, finish, passes_append kernelProgram firstPasses restPasses, represented⟩

theorem tm_halt_simulated {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (s : State) (rep : ScanRep machine c 0 s)
    (halted : TM.Halts machine c) : LoopHalts kernelProgram s := by
  rcases halted with ⟨n, next, completed, fault⟩
  rcases simulate_run machine n c next s rep completed with ⟨k, middle, history, nextRep⟩
  rcases simulate_halt machine next 0 middle nextRep fault with ⟨l, finish, _, tail, stopped⟩
  exact ⟨k + l, finish, passes_append kernelProgram history tail, stopped⟩

/-- A physical halt reflects an actual TM halt. A rejected candidate counts
as stuttering; a match is an actual TM step. Neither can create a false halt. -/
theorem kernel_halt_reflected {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (n : Nat) (c : TM.Configuration alphabet states) (index : Nat) (s finish : State)
    (rep : ScanRep machine c index s) (completed : Passes kernelProgram s finish n)
    (fault : run kernelProgram finish = none) : TM.Halts machine c := by
  induction n generalizing c index s finish with
  | zero =>
    cases completed
    exact ⟨0, c, rfl, kernel_fault_reflects machine c index s rep fault⟩
  | succ n ih =>
    cases completed with
    | succ first rest =>
      cases nextStep : scanStep machine (c, index) with
      | none =>
        have failed := scan_failure machine c index s rep nextStep
        rw [failed] at first
        cases first
      | some next =>
        rcases next with ⟨next, nextIndex⟩
        rcases scan_success machine c next index nextIndex s rep nextStep with
          ⟨actual, actualRun, actualRep⟩
        have same := Option.some.inj (actualRun.symm.trans first)
        have tail : Passes kernelProgram actual finish n := by rw [same]; exact rest
        have halted := ih next nextIndex actual finish actualRep tail fault
        rcases scan_success_semantic machine c next index nextIndex nextStep with unchanged | step
        · simpa [unchanged] using halted
        · rcases halted with ⟨k, finalConfig, history, stopped⟩
          exact ⟨k + 1, finalConfig, by simpa [TM.run, step] using history, stopped⟩

theorem kernel_halting_iff {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) :
    LoopHalts kernelProgram (initialKernelState machine c) ↔ TM.Halts machine c := by
  constructor
  · rintro ⟨n, finish, completed, fault⟩
    exact kernel_halt_reflected machine n c 0 _ finish (initial_scan_correct machine c) completed fault
  · exact tm_halt_simulated machine c _ (initial_scan_correct machine c)

theorem kernel_divergence_iff {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) :
    LoopDiverges kernelProgram (initialKernelState machine c) ↔ TM.Diverges machine c := by
  rw [loop_diverges_iff_not_halts, kernel_halting_iff, TM.diverges_iff_not_halts]

/-- A finite input and finite transition function determine the initial memory.
The same 64-MOV program simulates every such machine with one explicit backedge.
This theorem uses thirteen logical registers; four-register lowering is separate. -/
theorem fixed_mov_simulation : ∃ program : List Instruction, program.length = 64 ∧
    ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet)),
      let c := TM.initialConfiguration machine input
      (LoopHalts program (initialKernelState machine c) ↔ TM.Halts machine c) ∧
      (LoopDiverges program (initialKernelState machine c) ↔ TM.Diverges machine c) := by
  refine ⟨kernelProgram, kernel_length, ?_⟩
  intro alphabet states machine input
  exact ⟨kernel_halting_iff machine _, kernel_divergence_iff machine _⟩

end SmcTuring.Dolan.Mov

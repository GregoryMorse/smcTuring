module
public import SmcTuring.Dolan.Scan

public section

namespace SmcTuring.Dolan.Mov

open Encoding Table

theorem passes_append (program : List Instruction) {s middle finish : State} {first second : Nat}
    (a : Passes program s middle first) (b : Passes program middle finish second) :
    Passes program s finish (first + second) := by
  induction a with
  | zero => simpa using b
  | succ completed rest ih =>
    simpa [Nat.succ_add] using Passes.succ completed (ih b)

@[expose] def Resolution {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Nat) (s : State) : Prop :=
  ∃ n finish, n ≤ (entries machine c.state).length - index ∧ Passes kernelProgram s finish n ∧
    ((ScanRep machine c (entries machine c.state).length finish ∧ TM.step machine c = none) ∨
     (0 < n ∧ ∃ next, TM.step machine c = some next ∧ ScanRep machine next 0 finish))

/-- A scan cannot diverge internally: in at most alphabet-size complete
body passes it reaches either the TM successor or the halting sentinel. -/
theorem scan_resolves {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Nat) (s : State)
    (rep : ScanRep machine c index s) : Resolution machine c index s := by
  have solve : ∀ rank index s, (entries machine c.state).length - index = rank →
      ScanRep machine c index s → Resolution machine c index s := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro index s equal rep
      by_cases hi : index < (entries machine c.state).length
      · let entry := (entries machine c.state)[index]
        by_cases hm : entry.trigger = c.tape c.head
        · have scan : scanStep machine (c, index) = some (applyEntry c entry, 0) := by
            simp [scanStep, hi, entry] at hm ⊢
            exact hm
          rcases scan_success machine c (applyEntry c entry) index 0 s rep scan with
            ⟨finish, completed, represented⟩
          have member : entry ∈ entries machine c.state := List.getElem_mem hi
          have applicable := entries_sound machine c.state entry member
          rw [hm] at applicable
          have step : TM.step machine c = some (applyEntry c entry) :=
            TM.transition_correct machine c entry.symbol entry.direction entry.destination applicable
          exact ⟨1, finish, by omega, Passes.succ completed (Passes.zero finish),
            Or.inr ⟨by decide, applyEntry c entry, step, represented⟩⟩
        · have scan : scanStep machine (c, index) = some (c, index + 1) := by
            simp [scanStep, hi, entry] at hm ⊢
            exact hm
          rcases scan_success machine c c index (index + 1) s rep scan with
            ⟨middle, completed, nextRep⟩
          have smaller : (entries machine c.state).length - (index + 1) < rank := by
            rw [← equal]
            exact scan_rank_decreases machine c index hi
          rcases ih _ smaller (index + 1) middle rfl nextRep with ⟨n, finish, bound, rest, outcome⟩
          refine ⟨n + 1, finish, by omega, Passes.succ completed rest, ?_⟩
          rcases outcome with halted | ⟨_, next, step, represented⟩
          · exact Or.inl halted
          · exact Or.inr ⟨by omega, next, step, represented⟩
      · have exhausted : index = (entries machine c.state).length := by have := rep.2.2.1; omega
        subst index
        exact ⟨0, s, Nat.zero_le _, Passes.zero s, Or.inl ⟨rep, exhausted_halts machine c s rep⟩⟩
  exact solve _ index s rfl rep

theorem simulate_step {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c next : TM.Configuration alphabet states) (index : Nat) (s : State)
    (rep : ScanRep machine c index s) (step : TM.step machine c = some next) :
    ∃ n finish, 0 < n ∧ n ≤ (entries machine c.state).length - index ∧
      Passes kernelProgram s finish n ∧ ScanRep machine next 0 finish := by
  rcases scan_resolves machine c index s rep with ⟨n, finish, bound, completed, outcome⟩
  rcases outcome with ⟨_, halted⟩ | ⟨positive, actual, actualStep, represented⟩
  · rw [step] at halted
    cases halted
  · have equal : actual = next := Option.some.inj (actualStep.symm.trans step)
    subst actual
    exact ⟨n, finish, positive, bound, completed, represented⟩

theorem simulate_halt {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Nat) (s : State)
    (rep : ScanRep machine c index s) (step : TM.step machine c = none) :
    ∃ n finish, n ≤ (entries machine c.state).length - index ∧
      Passes kernelProgram s finish n ∧ run kernelProgram finish = none := by
  rcases scan_resolves machine c index s rep with ⟨n, finish, bound, completed, outcome⟩
  rcases outcome with ⟨represented, _⟩ | ⟨_, actual, actualStep, _⟩
  · have stopped : scanStep machine (c, (entries machine c.state).length) = none := by simp [scanStep]
    exact ⟨n, finish, bound, completed, scan_failure machine c _ finish represented stopped⟩
  · rw [step] at actualStep
    cases actualStep

theorem scan_success_semantic {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c next : TM.Configuration alphabet states) (index nextIndex : Nat)
    (h : scanStep machine (c, index) = some (next, nextIndex)) :
    next = c ∨ TM.step machine c = some next := by
  by_cases hi : index < (entries machine c.state).length
  · let entry := (entries machine c.state)[index]
    by_cases hm : entry.trigger = c.tape c.head
    · have same : (applyEntry c entry, 0) = (next, nextIndex) := by
        simpa [scanStep, hi, hm, entry] using h
      have applicable := entries_sound machine c.state entry (List.getElem_mem hi)
      rw [hm] at applicable
      have moved := TM.transition_correct machine c entry.symbol entry.direction entry.destination applicable
      exact Or.inr (moved.trans (congrArg some (congrArg Prod.fst same)))
    · have same : (c, index + 1) = (next, nextIndex) := by
        simpa [scanStep, hi, hm, entry] using h
      exact Or.inl (congrArg Prod.fst same).symm
  · simp [scanStep, hi] at h

theorem kernel_fault_reflects {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Nat) (s : State)
    (rep : ScanRep machine c index s) (fault : run kernelProgram s = none) : TM.step machine c = none := by
  cases h : scanStep machine (c, index) with
  | none =>
    have exhausted : index = (entries machine c.state).length := by
      by_cases hi : index < (entries machine c.state).length
      · simp only [scanStep, hi, ↓reduceDIte] at h
        split at h <;> cases h
      · have := rep.2.2.1
        omega
    subst index
    exact exhausted_halts machine c s rep
  | some next =>
    rcases next with ⟨next, nextIndex⟩
    rcases scan_success machine c next index nextIndex s rep h with ⟨finish, completed, _⟩
    rw [fault] at completed
    cases completed

end SmcTuring.Dolan.Mov

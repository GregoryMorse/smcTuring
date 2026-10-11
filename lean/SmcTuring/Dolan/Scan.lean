module
public import SmcTuring.Dolan.Kernel

public section

namespace SmcTuring.Dolan.Mov

open Encoding Table

@[expose] def ScanRep {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Nat) (s : State) : Prop :=
  RuntimeRep machine c s ∧ s.registers .transition = .address (cursor machine c.state index) ∧
    index ≤ (entries machine c.state).length ∧
    ∀ j : Fin (entries machine c.state).length, j.val < index →
      (entries machine c.state)[j.val].trigger ≠ c.tape c.head

@[expose] def scanStep {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (v : TM.Configuration alphabet states × Nat) : Option (TM.Configuration alphabet states × Nat) :=
  if h : v.2 < (entries machine v.1.state).length then
    let entry := (entries machine v.1.state)[v.2]
    if entry.trigger = v.1.tape v.1.head then some (applyEntry v.1 entry, 0)
    else some (v.1, v.2 + 1)
  else none

theorem scan_iteration {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Nat) (s : State)
    (rep : ScanRep machine c index s) :
    match scanStep machine (c, index) with
    | none => run kernelProgram s = none
    | some (next, nextIndex) => ∃ finish, run kernelProgram s = some finish ∧
        ScanRep machine next nextIndex finish := by
  by_cases hi : index < (entries machine c.state).length
  · let j : Fin (entries machine c.state).length := ⟨index, hi⟩
    have ht : s.registers .transition = .address (node alphabet c.state index) := by
      simpa [cursor, hi] using rep.2.1
    rcases kernel_candidate_correct machine c j s rep.1 ht with ⟨finish, completed, runtime, target⟩
    by_cases hm : (entries machine c.state)[index].trigger = c.tape c.head
    · simp only [scanStep, hi, ↓reduceDIte, hm, ↓reduceIte]
      have runtime' : RuntimeRep machine (applyEntry c (entries machine c.state)[index]) finish := by
        simpa [j, hm] using runtime
      have target' : finish.registers .transition =
          .address (cursor machine (applyEntry c (entries machine c.state)[index]).state 0) := by
        simpa [j, hm, head, applyEntry] using target
      exact ⟨finish, completed, runtime', target', Nat.zero_le _, by intro k hk; omega⟩
    · simp only [scanStep, hi, ↓reduceDIte, hm, ↓reduceIte]
      have runtime' : RuntimeRep machine c finish := by simpa [j, hm] using runtime
      have target' : finish.registers .transition = .address (cursor machine c.state (index + 1)) := by
        simpa [j, hm] using target
      refine ⟨finish, completed, runtime', target', by omega, ?_⟩
      intro k hk
      by_cases earlier : k.val < index
      · exact rep.2.2.2 k earlier
      · have equal : k = j := Fin.ext (by simp only [j]; omega)
        subst k
        exact hm
  · simp only [scanStep, hi, ↓reduceDIte]
    have ht : s.registers .transition = .address 0 := by simpa [cursor, hi] using rep.2.1
    exact kernel_sentinel_traps machine c s rep.1 ht

theorem scan_success {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c next : TM.Configuration alphabet states) (index nextIndex : Nat) (s : State)
    (rep : ScanRep machine c index s) (h : scanStep machine (c, index) = some (next, nextIndex)) :
    ∃ finish, run kernelProgram s = some finish ∧ ScanRep machine next nextIndex finish := by
  have correct := scan_iteration machine c index s rep
  simpa [h] using correct

theorem scan_failure {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Nat) (s : State)
    (rep : ScanRep machine c index s) (h : scanStep machine (c, index) = none) :
    run kernelProgram s = none := by
  have correct := scan_iteration machine c index s rep
  simpa [h] using correct

/-- Every scanned prefix contains only rejected symbols. Exhaustion therefore
means that the TM has no applicable transition, rather than a spurious failure. -/
theorem exhausted_halts {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (s : State)
    (rep : ScanRep machine c (entries machine c.state).length s) : TM.step machine c = none := by
  apply TM.missing_transition_halts
  apply (missing_transition_iff machine c.state (c.tape c.head)).2
  intro entry member
  rcases List.getElem_of_mem member with ⟨i, hi, equal⟩
  have skipped := rep.2.2.2 ⟨i, hi⟩ hi
  simpa [equal] using skipped

/-- Each rejected candidate reduces this finite rank by exactly one. -/
theorem scan_rank_decreases {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Nat) (hi : index < (entries machine c.state).length) :
    (entries machine c.state).length - (index + 1) < (entries machine c.state).length - index := by omega

@[expose] def initialKernelState {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) : State :=
  { registers := fun r => match r with
      | .scratch => .address 0
      | .zero => .offset false
      | .one => .offset true
      | .transition => .address (head machine c.state)
      | .current => .address ((tapeLayout alphabet states).cell c.head)
      | .left => .address ((tapeLayout alphabet states).cell (c.head - 1))
      | .right => .address ((tapeLayout alphabet states).cell (c.head + 1))
      | _ => .offset false
    memory := initialMemory machine c }

theorem initial_scan_correct {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) : ScanRep machine c 0 (initialKernelState machine c) := by
  refine ⟨⟨?_, ?_, initial_table_correct machine c⟩, rfl, Nat.zero_le _, ?_⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, initial_memory_tape_correct machine c⟩
  · intro j hj
    omega

end SmcTuring.Dolan.Mov

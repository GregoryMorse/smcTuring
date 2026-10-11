module
public import SmcTuring.SMC.ConcreteGuardEffects

public section

namespace SmcTuring.SMC.Concrete

open Dolan

@[expose] def guardEntryResult (sense : Bool) (s : State) : State :=
  run 1 (callProgram (.fixed (guardPC sense))) s

theorem guard_entry_effect (sense : Bool) (s : State) (ready : Static s) : guardEntryResult sense s =
    { s with stack := returnField, pc := guardPC sense, memory := write s.memory returnField (s.pc + 3) } :=
  reset_call_correct 1 topField returnField (guardPC sense) s (static_top s ready)

theorem guard_entry_static (sense : Bool) (s : State) (ready : Static s) : Static (guardEntryResult sense s) := by
  simpa only [Static, guard_entry_effect sense s ready, returnField] using
    static_dynamic_write s 26 (s.pc + 3) ready (by decide)

theorem guard_entry_source (source : Mov.State) (sense : Bool) (s : State) (ready : Static s)
    (rep : Virtual.Rep dataLayout source s) : Virtual.Rep dataLayout source (guardEntryResult sense s) := by
  simpa only [Virtual.Rep, guard_entry_effect sense s ready, returnField] using
    metadata_source_frame source s 26 (s.pc + 3) rep

theorem guard_entry_execute (sense : Bool) (s : State) (ready : Static s)
    (site : LinearAt image s.pc (callProgram (.fixed (guardPC sense)))) : Executes 3 s (guardEntryResult sense s) := by
  apply reset_call_image 1 image topField returnField (.fixed (guardPC sense)) s
  · exact ⟨site.1, site.2.1, trivial⟩
  · simpa [Int.add_assoc] using site.2.2.1
  · exact static_top s ready
  · exact meta_is_code 25 (by decide)
  · exact meta_is_code 26 (by decide)

@[expose] def guardInvocationResult (sense : Bool) (s : State) : State := guardResult sense (guardEntryResult sense s)

/-- Caller and shared callee take exactly 89 fetched, code-writing instructions.
Only the caller snippet's placement remains a composition premise. -/
theorem guard_invocation_execute (sense : Bool) (s : State) (ready : Static s)
    (site : LinearAt image s.pc (callProgram (.fixed (guardPC sense)))) :
    Executes 89 s (guardInvocationResult sense s) ∧ Static (guardInvocationResult sense s) := by
  have entry := guard_entry_execute sense s ready site
  have callee := guard_execute sense (guardEntryResult sense s) (guard_entry_static sense s ready)
    (by rw [guard_entry_effect sense s ready])
  exact ⟨entry.trans callee.1, callee.2⟩

theorem guard_invocation_source (source : Mov.State) (sense : Bool) (s : State) (ready : Static s)
    (rep : Virtual.Rep dataLayout source s) : Virtual.Rep dataLayout source (guardInvocationResult sense s) := by
  apply guard_source_frame source sense (guardEntryResult sense s) (guard_entry_static sense s ready)
  · rw [guard_entry_effect sense s ready]
  · exact guard_entry_source source sense s ready rep

theorem guard_invocation_pc (sense : Bool) (s : State) (ready : Static s) :
    (guardInvocationResult sense s).pc =
      if s.memory candidateField < 13 then (if sense then s.pc + 3 else terminalPC)
      else (if sense then terminalPC else s.pc + 3) := by
  rw [guardInvocationResult, guard_target_pc sense (guardEntryResult sense s) (guard_entry_static sense s ready)
    (by rw [guard_entry_effect sense s ready])]
  simp [guardTarget, guard_entry_effect sense s ready, write, candidateField, returnField, metaField]
  rfl

theorem guard_invocation_terminal_iff (sense : Bool) (s : State) (ready : Static s)
    (separate : s.pc + 3 ≠ terminalPC) :
    (guardInvocationResult sense s).pc = terminalPC ↔
      if sense then 13 ≤ s.memory candidateField else s.memory candidateField < 13 := by
  rw [guard_invocation_pc sense s ready]
  cases sense <;> by_cases below : s.memory candidateField < 13 <;> simp [below, separate] <;> omega

theorem terminal_observation (s : State) (pc : s.pc = terminalPC) : step 1 image s = none := by
  simp [step, fetch, pc, terminal_missing]

theorem guard_invocation_memory_frame (sense : Bool) (s : State) (ready : Static s) (field : Int)
    (returned : field ≠ returnField) (resume : field ≠ resumeField) (scratch : field ≠ scratchField)
    (mask : field ≠ maskField) (selected : field ≠ selectedField) :
    (guardInvocationResult sense s).memory field = s.memory field := by
  rw [guardInvocationResult, guard_memory_frame sense (guardEntryResult sense s) (guard_entry_static sense s ready)
      (by rw [guard_entry_effect sense s ready]) field returned resume scratch mask selected,
      guard_entry_effect sense s ready]
  exact read_write_other _ _ _ _ returned

end SmcTuring.SMC.Concrete

module
public import SmcTuring.SMC.ConcreteGuards

public section

namespace SmcTuring.SMC.Concrete

/-- The offset guard returns exactly for tags below the heap boundary. The
base guard returns exactly for calculated pointers at or above that boundary. -/
@[expose] def guardTarget (sense : Bool) (s : State) : Int :=
  if s.memory candidateField < 13 then
    if sense then s.memory returnField else terminalPC
  else if sense then terminalPC else s.memory returnField

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem guard_prefix_selected (sense : Bool) (s : State) (ready : Static s) :
    (guardPrefix sense s).memory selectedField = guardTarget sense s := by
  have r13 := static_reader_label s 13 ready (by decide)
  have r14 := static_reader_label s 14 ready (by decide)
  have r15 := static_reader_label s 15 ready (by decide)
  have r16 := static_reader_label s 16 ready (by decide)
  have r17 := static_reader_label s 17 ready (by decide)
  have r18 := static_reader_label s 18 ready (by decide)
  have boundary := ready 28 (by decide)
  have zero := ready 29 (by decide)
  have terminal := ready 31 (by decide)
  have capture := static_capture s sense ready
  simp [readerLabel, metadataValue, candidateField, boundaryField, zeroField, resumeField,
    terminalField, maskField, metaField, dataLayout, heapBase, fieldAddress] at r13 r14 r15 r16 r17 r18 boundary zero terminal
  by_cases below : s.memory (-28) < 13
  all_goals cases sense <;>
    simp [captureLabel, metaField, returnField] at capture <;>
    simp [guardPrefix, guardReadResult, guardRead, guard_capture_effect, readOpResult,
      readInvocationResult, guardSbbResult, execute, decode, Address.eval, Operation.header,
      readerLabel, readerPC, captureLabel, resumeField, returnField, scratchField, maskField,
      selectedField, candidateField, metaField, write, r13, r14, r15, r16, r17, r18,
      boundary, zero, terminal, capture, borrowWord, guardTarget, below]
  all_goals first | exact select_word _ _ true | exact select_word _ _ false

theorem guard_target_pc (sense : Bool) (s : State) (ready : Static s) (pc : s.pc = guardPC sense) :
    (guardResult sense s).pc = guardTarget sense s := by
  have stages := guard_prefix_execute sense s ready pc
  rw [guardResult, guard_call_effect _ stages.2.1]
  exact guard_prefix_selected sense s ready

theorem guard_returns_iff (sense : Bool) (s : State) (ready : Static s) (pc : s.pc = guardPC sense)
    (resumeSeparate : s.memory returnField ≠ terminalPC) :
    (guardResult sense s).pc = s.memory returnField ↔
      if sense then s.memory candidateField < 13 else 13 ≤ s.memory candidateField := by
  rw [guard_target_pc sense s ready pc]
  cases sense <;> by_cases below : s.memory candidateField < 13 <;>
    simp [guardTarget, below, Ne.symm resumeSeparate] <;> omega

theorem guard_terminal_iff (sense : Bool) (s : State) (ready : Static s) (pc : s.pc = guardPC sense)
    (resumeSeparate : s.memory returnField ≠ terminalPC) :
    (guardResult sense s).pc = terminalPC ↔
      if sense then 13 ≤ s.memory candidateField else s.memory candidateField < 13 := by
  rw [guard_target_pc sense s ready pc]
  cases sense <;> by_cases below : s.memory candidateField < 13 <;>
    simp [guardTarget, below, resumeSeparate] <;> omega

end SmcTuring.SMC.Concrete

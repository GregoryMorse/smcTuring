module
public import SmcTuring.SMC.ConcreteInitialization

public section

namespace SmcTuring.SMC.Concrete

open Dolan

theorem static_reader_label (s : State) (reader : Nat) (ready : Static s) (bounded : reader < 22) :
    s.memory (readerLabel reader) = metadataValue reader := by
  exact ready reader (by simp only [StaticSlot]; omega)

theorem static_reader_target_code (reader : Nat) (bounded : reader < 22) :
    image.codeField (metadataValue reader) := by
  by_cases register : reader < 13
  · simp only [metadataValue, register, ite_true]
    exact data_is_code _ (by omega)
  · have choices : reader = 13 ∨ reader = 14 ∨ reader = 15 ∨ reader = 16 ∨ reader = 17 ∨
        reader = 18 ∨ reader = 19 ∨ reader = 20 ∨ reader = 21 := by omega
    rcases choices with h | h | h | h | h | h | h | h | h <;> subst reader <;>
      simp only [image, Code] <;> decide

theorem static_reader_target_separate (reader : Nat) (bounded : reader < 22) : metadataValue reader ≠ returnField := by
  by_cases register : reader < 13
  · simp only [metadataValue, register, ite_true, returnField, metaField]
    omega
  · have choices : reader = 13 ∨ reader = 14 ∨ reader = 15 ∨ reader = 16 ∨ reader = 17 ∨
        reader = 18 ∨ reader = 19 ∨ reader = 20 ∨ reader = 21 := by omega
    rcases choices with h | h | h | h | h | h | h | h | h <;> subst reader <;> decide

/-- Source call sites are structural snippets of the already constructed image.
The callee placement, code ownership, constant value and separation facts are
proved here and no longer passed through as simulator assumptions. -/
theorem call_ready (s : State) (reader : Nat) (ready : Static s) (bounded : reader < 23)
    (site : LinearAt image s.pc (callProgram (.fixed (readerPC reader))))
    (targetCode : image.codeField (s.memory (readerLabel reader)))
    (targetSeparate : s.memory (readerLabel reader) ≠ returnField) :
    ReadCallReady 1 image (readerLabel reader) (readerPC reader) topField returnField s := by
  have reset : LinearAt image s.pc (stackResetProgram topField) := ⟨site.1, site.2.1, trivial⟩
  have call : image.headers (s.pc + 2) = some (.call (.fixed (readerPC reader)), s.pc + 3) := by
    simpa [Int.add_assoc] using site.2.2.1
  have labelSeparate : readerLabel reader ≠ returnField := by
    simp only [readerLabel, returnField, metaField]
    omega
  exact ⟨reader_placement reader bounded, reset, call, static_top s ready,
    by decide, labelSeparate, targetSeparate, meta_is_code 25 (by decide),
    meta_is_code 26 (by decide), meta_is_code reader (by omega), targetCode⟩

theorem static_call_ready (s : State) (reader : Nat) (ready : Static s) (bounded : reader < 22)
    (site : LinearAt image s.pc (callProgram (.fixed (readerPC reader)))) :
    ReadCallReady 1 image (readerLabel reader) (readerPC reader) topField returnField s := by
  apply call_ready s reader ready (by omega) site
  · rw [static_reader_label s reader ready bounded]
    exact static_reader_target_code reader bounded
  · rw [static_reader_label s reader ready bounded]
    exact static_reader_target_separate reader bounded

theorem read_static_frame (s : State) (reader : Nat) (ready : Static s) :
    Static (readInvocationResult (readerLabel reader) (readerPC reader) returnField s) := by
  have frame := static_dynamic_write s 26 (readerPC reader + 7) ready (by decide)
  simpa only [Static, readInvocationResult, returnField] using frame

theorem read_source_frame (source : Mov.State) (s : State) (reader : Nat)
    (rep : Virtual.Rep dataLayout source s) :
    Virtual.Rep dataLayout source (readInvocationResult (readerLabel reader) (readerPC reader) returnField s) :=
  Virtual.read_invocation_rep dataLayout source s (readerLabel reader) (readerPC reader) returnField rep
    (metadata_outside_data 26)

theorem static_read_image (s : State) (reader : Nat) (ready : Static s) (bounded : reader < 22)
    (site : LinearAt image s.pc (callProgram (.fixed (readerPC reader)))) :
    runImage 1 image 10 s = some (readInvocationResult (readerLabel reader) (readerPC reader) returnField s) ∧
      PureSteps 1 image 10 s ∧
      Static (readInvocationResult (readerLabel reader) (readerPC reader) returnField s) := by
  have executed := (static_call_ready s reader ready bounded site).correct 1 image
    (readerLabel reader) (readerPC reader) topField returnField s
  exact ⟨executed.1, executed.2, read_static_frame s reader ready⟩

end SmcTuring.SMC.Concrete

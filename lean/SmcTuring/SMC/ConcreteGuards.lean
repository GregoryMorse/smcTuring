module
public import SmcTuring.SMC.ConcretePlacement

public section

namespace SmcTuring.SMC.Concrete

open Dolan

@[expose] def Executes (count : Nat) (start finish : State) : Prop :=
  runImage 1 image count start = some finish ∧ PureSteps 1 image count start

theorem Executes.trans {first second : Nat} {start middle finish : State}
    (a : Executes first start middle) (b : Executes second middle finish) : Executes (first + second) start finish := by
  constructor
  · rw [run_image_add, a.1, Option.bind_some]
    exact b.1
  · exact (pure_steps_composition 1 image first second start middle a.1).mpr ⟨a.2, b.2⟩

theorem metadata_source_frame (source : Mov.State) (s : State) (index : Nat) (datum : Int)
    (rep : Virtual.Rep dataLayout source s) :
    Virtual.Rep dataLayout source { s with memory := write s.memory (metaField index) datum } := by
  apply Virtual.metadata_write_frame dataLayout source s (metaField index) datum rep
  · intro r
    exact data_field_separate _ _ _ (metadata_outside_data index) (Virtual.register_is_code dataLayout r)
  · intro p
    exact data_field_separate _ _ _ (metadata_outside_data index) (heap_is_code dataLayout.data p)

@[expose] def guardCaptureResult (sense : Bool) (s : State) : State := run 1 (guardCaptureProgram sense) s

theorem guard_capture_effect (sense : Bool) (s : State) : guardCaptureResult sense s =
    { s with
      acc := s.memory (s.memory (captureLabel sense))
      memory := write s.memory resumeField (s.memory (s.memory (captureLabel sense)))
      pc := s.pc + 5 } := by
  rw [guardCaptureResult, guardCaptureProgram, run_append, read_correct]
  simp [run, decode, Address.eval, execute, Int.add_assoc]

theorem guard_capture_pc (sense : Bool) (s : State) : (guardCaptureResult sense s).pc = s.pc + 5 := by
  rw [guard_capture_effect]

theorem guard_capture_static (sense : Bool) (s : State) (ready : Static s) : Static (guardCaptureResult sense s) := by
  simpa only [Static, guard_capture_effect, resumeField] using
    static_dynamic_write s 30 (s.memory (s.memory (captureLabel sense))) ready (by decide)

theorem guard_capture_source (source : Mov.State) (sense : Bool) (s : State) (rep : Virtual.Rep dataLayout source s) :
    Virtual.Rep dataLayout source (guardCaptureResult sense s) := by
  simpa only [Virtual.Rep, guard_capture_effect, resumeField] using
    metadata_source_frame source s 30 (s.memory (s.memory (captureLabel sense))) rep

theorem guard_capture_execute (sense : Bool) (s : State) (ready : Static s) (pc : s.pc = guardPC sense) :
    Executes 5 s (guardCaptureResult sense s) := by
  have placed : LinearAt image s.pc (guardCaptureProgram sense) := by rw [pc]; exact guard_capture_site sense
  have sequential : NonBranching (guardCaptureProgram sense) := by
    simp [NonBranching, guardCaptureProgram, readProgram, Header.Sequential]
  have executed := linear_image_execution 1 image (guardCaptureProgram sense) s placed sequential
  refine ⟨executed.1, executed.2.mpr ?_⟩
  rw [guardCaptureProgram, pure_append]
  constructor
  · apply read_pure
    · cases sense <;> exact meta_is_code _ (by decide)
    · rw [static_capture s sense ready]
      exact meta_is_code 26 (by decide)
  · simpa [PureRun, WritesCode, decode, Address.eval, footprint, resumeField] using meta_is_code 30 (by decide)

@[expose] def guardReadResult (sense : Bool) (index : Fin 7) (s : State) : State :=
  readOpResult (guardRead sense index).reader (guardRead sense index).operation s

theorem guard_read_pc (sense : Bool) (index : Fin 7) (s : State) : (guardReadResult sense index s).pc = s.pc + 4 :=
  read_op_pc _ _ s

theorem guard_read_static (sense : Bool) (index : Fin 7) (s : State) (ready : Static s) :
    Static (guardReadResult sense index s) :=
  read_op_static_frame _ _ s ready (guard_read_dynamic sense index)

theorem guard_read_source (source : Mov.State) (sense : Bool) (index : Fin 7) (s : State)
    (rep : Virtual.Rep dataLayout source s) : Virtual.Rep dataLayout source (guardReadResult sense index s) :=
  read_op_source_frame source _ _ s rep (guard_read_outside sense index)

theorem guard_read_execute (sense : Bool) (index : Fin 7) (s : State) (ready : Static s)
    (pc : s.pc = guardPC sense + ((guardRead sense index).start : Int)) :
    Executes 11 s (guardReadResult sense index s) := by
  apply read_op_correct s _ _ ready (guard_read_bounded sense index)
  · rw [pc]
    exact guard_read_site sense index
  · exact guard_read_code sense index

@[expose] def guardSbbResult (s : State) : State :=
  execute 1 (.subtractBorrowZero maskField) (s.pc + 1) s

theorem guard_sbb_pc (s : State) : (guardSbbResult s).pc = s.pc + 1 := rfl

theorem guard_sbb_static (s : State) (ready : Static s) : Static (guardSbbResult s) :=
  static_dynamic_write s 32 (s.memory maskField - borrowWord s.carry) ready (by decide)

theorem guard_sbb_source (source : Mov.State) (s : State) (rep : Virtual.Rep dataLayout source s) :
    Virtual.Rep dataLayout source (guardSbbResult s) :=
  metadata_source_frame source s 32 (s.memory maskField - borrowWord s.carry) rep

theorem guard_sbb_execute (sense : Bool) (s : State) (pc : s.pc = guardPC sense + 17) : Executes 1 s (guardSbbResult s) := by
  have placed : image.headers s.pc = some (.subtractBorrowZero maskField, s.pc + 1) := by
    simpa [pc, Int.add_assoc] using guard_sbb_site sense
  have executed := image_single 1 image (.subtractBorrowZero maskField) (s.pc + 1) s placed
  refine ⟨executed.1, executed.2.mpr ?_⟩
  simpa [WritesCode, footprint, decode, maskField] using meta_is_code 32 (by decide)

@[expose] def guardCallResult (s : State) : State := run 1 (callProgram (.operand selectedField)) s

theorem guard_call_effect (s : State) (ready : Static s) : guardCallResult s =
    { s with stack := returnField, pc := s.memory selectedField, memory := write s.memory returnField (s.pc + 3) } :=
  reset_call_operand_correct 1 topField returnField selectedField s (static_top s ready)

theorem guard_call_static (s : State) (ready : Static s) : Static (guardCallResult s) := by
  simpa only [Static, guard_call_effect s ready, returnField] using static_dynamic_write s 26 (s.pc + 3) ready (by decide)

theorem guard_call_source (source : Mov.State) (s : State) (ready : Static s) (rep : Virtual.Rep dataLayout source s) :
    Virtual.Rep dataLayout source (guardCallResult s) := by
  simpa only [Virtual.Rep, guard_call_effect s ready, returnField] using metadata_source_frame source s 26 (s.pc + 3) rep

theorem guard_call_execute (sense : Bool) (s : State) (ready : Static s) (pc : s.pc = guardPC sense + 34) :
    Executes 3 s (guardCallResult s) := by
  have site : LinearAt image s.pc (callProgram (.operand selectedField)) := by rw [pc]; exact guard_final_call_site sense
  apply reset_call_image 1 image topField returnField (.operand selectedField) s
  · exact ⟨site.1, site.2.1, trivial⟩
  · simpa [Int.add_assoc] using site.2.2.1
  · exact static_top s ready
  · exact meta_is_code 25 (by decide)
  · exact meta_is_code 26 (by decide)

@[expose] def guardPrefix (sense : Bool) (s : State) : State :=
  let s0 := guardCaptureResult sense s
  let s1 := guardReadResult sense ⟨0, by decide⟩ s0
  let s2 := guardReadResult sense ⟨1, by decide⟩ s1
  let s3 := guardReadResult sense ⟨2, by decide⟩ s2
  let s4 := guardSbbResult s3
  let s5 := guardReadResult sense ⟨3, by decide⟩ s4
  let s6 := guardReadResult sense ⟨4, by decide⟩ s5
  let s7 := guardReadResult sense ⟨5, by decide⟩ s6
  guardReadResult sense ⟨6, by decide⟩ s7

@[expose] def guardResult (sense : Bool) (s : State) : State := guardCallResult (guardPrefix sense s)

theorem guard_prefix_execute (sense : Bool) (s : State) (ready : Static s) (pc : s.pc = guardPC sense) :
    Executes 83 s (guardPrefix sense s) ∧ Static (guardPrefix sense s) ∧ (guardPrefix sense s).pc = guardPC sense + 34 := by
  let s0 := guardCaptureResult sense s
  let s1 := guardReadResult sense 0 s0
  let s2 := guardReadResult sense 1 s1
  let s3 := guardReadResult sense 2 s2
  let s4 := guardSbbResult s3
  let s5 := guardReadResult sense 3 s4
  let s6 := guardReadResult sense 4 s5
  let s7 := guardReadResult sense 5 s6
  let s8 := guardReadResult sense 6 s7
  have r0 := guard_capture_static sense s ready
  have r1 := guard_read_static sense 0 s0 r0
  have r2 := guard_read_static sense 1 s1 r1
  have r3 := guard_read_static sense 2 s2 r2
  have r4 := guard_sbb_static s3 r3
  have r5 := guard_read_static sense 3 s4 r4
  have r6 := guard_read_static sense 4 s5 r5
  have r7 := guard_read_static sense 5 s6 r6
  have r8 := guard_read_static sense 6 s7 r7
  have p0 : s0.pc = guardPC sense + 5 := by simp only [s0, guard_capture_pc, pc]
  have p1 : s1.pc = guardPC sense + 9 := by simp [s1, guard_read_pc, p0, Int.add_assoc]
  have p2 : s2.pc = guardPC sense + 13 := by simp [s2, guard_read_pc, p1, Int.add_assoc]
  have p3 : s3.pc = guardPC sense + 17 := by simp [s3, guard_read_pc, p2, Int.add_assoc]
  have p4 : s4.pc = guardPC sense + 18 := by simp [s4, guard_sbb_pc, p3, Int.add_assoc]
  have p5 : s5.pc = guardPC sense + 22 := by simp [s5, guard_read_pc, p4, Int.add_assoc]
  have p6 : s6.pc = guardPC sense + 26 := by simp [s6, guard_read_pc, p5, Int.add_assoc]
  have p7 : s7.pc = guardPC sense + 30 := by simp [s7, guard_read_pc, p6, Int.add_assoc]
  have p8 : s8.pc = guardPC sense + 34 := by simp [s8, guard_read_pc, p7, Int.add_assoc]
  have e0 := guard_capture_execute sense s ready pc
  have e1 := guard_read_execute sense 0 s0 r0 p0
  have e2 := guard_read_execute sense 1 s1 r1 p1
  have e3 := guard_read_execute sense 2 s2 r2 p2
  have e4 := guard_sbb_execute sense s3 p3
  have e5 := guard_read_execute sense 3 s4 r4 p4
  have e6 := guard_read_execute sense 4 s5 r5 p5
  have e7 := guard_read_execute sense 5 s6 r6 p6
  have e8 := guard_read_execute sense 6 s7 r7 p7
  exact ⟨(((((((e0.trans e1).trans e2).trans e3).trans e4).trans e5).trans e6).trans e7).trans e8, r8, p8⟩

theorem guard_prefix_source (source : Mov.State) (sense : Bool) (s : State) (rep : Virtual.Rep dataLayout source s) :
    Virtual.Rep dataLayout source (guardPrefix sense s) := by
  unfold guardPrefix
  apply guard_read_source
  apply guard_read_source
  apply guard_read_source
  apply guard_read_source
  apply guard_sbb_source
  apply guard_read_source
  apply guard_read_source
  apply guard_read_source
  exact guard_capture_source source sense s rep

/-- All 86 callee instructions are fetched from the constructed image. Every
instruction writes an owned operand field; the represented source state survives. -/
theorem guard_execute (sense : Bool) (s : State) (ready : Static s) (pc : s.pc = guardPC sense) :
    Executes 86 s (guardResult sense s) ∧ Static (guardResult sense s) := by
  have stages := guard_prefix_execute sense s ready pc
  have finalCall := guard_call_execute sense (guardPrefix sense s) stages.2.1 stages.2.2
  exact ⟨stages.1.trans finalCall, guard_call_static _ stages.2.1⟩

theorem guard_source_frame (source : Mov.State) (sense : Bool) (s : State) (ready : Static s)
    (pc : s.pc = guardPC sense) (rep : Virtual.Rep dataLayout source s) :
    Virtual.Rep dataLayout source (guardResult sense s) := by
  have stages := guard_prefix_execute sense s ready pc
  exact guard_call_source source (guardPrefix sense s) stages.2.1 (guard_prefix_source source sense s rep)

theorem guard_read_memory_frame (sense : Bool) (index : Fin 7) (s : State) (field : Int)
    (returned : field ≠ returnField) (scratch : field ≠ scratchField) (mask : field ≠ maskField)
    (selected : field ≠ selectedField) : (guardReadResult sense index s).memory field = s.memory field := by
  apply read_op_memory_frame _ _ s field returned
  rcases index with ⟨index, bounded⟩
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 := by omega
  rcases choices with h | h | h | h | h | h | h <;> subst index <;> cases sense <;>
    first | exact scratch | exact mask | exact selected

theorem guard_capture_memory_frame (sense : Bool) (s : State) (field : Int) (resume : field ≠ resumeField) :
    (guardCaptureResult sense s).memory field = s.memory field := by simp [guard_capture_effect, write, resume]

theorem guard_sbb_memory_frame (s : State) (field : Int) (mask : field ≠ maskField) :
    (guardSbbResult s).memory field = s.memory field := by simp [guardSbbResult, execute, write, mask]

theorem guard_prefix_memory_frame (sense : Bool) (s : State) (field : Int)
    (returned : field ≠ returnField) (resume : field ≠ resumeField) (scratch : field ≠ scratchField)
    (mask : field ≠ maskField) (selected : field ≠ selectedField) :
    (guardPrefix sense s).memory field = s.memory field := by
  unfold guardPrefix
  rw [guard_read_memory_frame sense ⟨6, by decide⟩ _ field returned scratch mask selected,
      guard_read_memory_frame sense ⟨5, by decide⟩ _ field returned scratch mask selected,
      guard_read_memory_frame sense ⟨4, by decide⟩ _ field returned scratch mask selected,
      guard_read_memory_frame sense ⟨3, by decide⟩ _ field returned scratch mask selected,
      guard_sbb_memory_frame _ field mask,
      guard_read_memory_frame sense ⟨2, by decide⟩ _ field returned scratch mask selected,
      guard_read_memory_frame sense ⟨1, by decide⟩ _ field returned scratch mask selected,
      guard_read_memory_frame sense ⟨0, by decide⟩ _ field returned scratch mask selected,
      guard_capture_memory_frame sense s field resume]

theorem guard_memory_frame (sense : Bool) (s : State) (ready : Static s) (pc : s.pc = guardPC sense) (field : Int)
    (returned : field ≠ returnField) (resume : field ≠ resumeField) (scratch : field ≠ scratchField)
    (mask : field ≠ maskField) (selected : field ≠ selectedField) :
    (guardResult sense s).memory field = s.memory field := by
  have stages := guard_prefix_execute sense s ready pc
  rw [guardResult, guard_call_effect _ stages.2.1]
  simp only [read_write_other _ _ _ _ returned]
  exact guard_prefix_memory_frame sense s field returned resume scratch mask selected

end SmcTuring.SMC.Concrete

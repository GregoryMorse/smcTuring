module
public import SmcTuring.SMC.ConcreteMetadataOps

public section

namespace SmcTuring.SMC.Concrete

open Dolan

@[expose] def offsetReadResult (offset : Mov.Register) (s : State) : State :=
  readOpResult (Four.slot offset).val (.assign candidateField) s

@[expose] def offsetGuardResult (offset : Mov.Register) (s : State) : State :=
  guardInvocationResult true (offsetReadResult offset s)

structure OffsetGuardSpec (source : Mov.State) (offset : Mov.Register) (start finish : State) : Prop where
  executed : Executes 100 start finish
  static : Static finish
  represented : Virtual.Rep dataLayout source finish
  pc : finish.pc = if encodeWord dataLayout.data (source.registers offset) < 13 then start.pc + 7 else terminalPC
  candidate : finish.memory candidateField = encodeWord dataLayout.data (source.registers offset)

theorem offset_guard_correct (source : Mov.State) (offset : Mov.Register) (s : State)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (readSite : LinearAt image s.pc (readOp (Four.slot offset).val (.store (.fixed candidateField))))
    (guardSite : LinearAt image (s.pc + 4) (callProgram (.fixed (guardPC true)))) :
    OffsetGuardSpec source offset s (offsetGuardResult offset s) := by
  let middle := offsetReadResult offset s
  have middleStatic : Static middle := read_op_metadata_static _ _ s 27 ready (by decide) rfl
  have middleRep : Virtual.Rep dataLayout source middle := read_op_metadata_source source _ _ s 27 rep rfl
  have middlePC : middle.pc = s.pc + 4 := read_op_pc _ _ s
  have loaded : middle.memory candidateField = encodeWord dataLayout.data (source.registers offset) := by
    rw [show middle = readOpResult (Four.slot offset).val (.assign candidateField) s by rfl, read_op_assign_value]
    exact register_reader_value source s offset ready rep
  have first : Executes 11 s middle := read_op_correct s _ _ ready (by have := (Four.slot offset).isLt; omega)
    readSite (meta_is_code 27 (by decide))
  have second := guard_invocation_execute true middle middleStatic (by rw [middlePC]; exact guardSite)
  refine ⟨first.trans second.1, second.2, guard_invocation_source source true middle middleStatic middleRep, ?_, ?_⟩
  · rw [show offsetGuardResult offset s = guardInvocationResult true middle by rfl,
      guard_invocation_pc true middle middleStatic, loaded, middlePC]
    simp [Int.add_assoc]
  · rw [show offsetGuardResult offset s = guardInvocationResult true middle by rfl,
      guard_candidate_frame true middle middleStatic, loaded]

@[expose] def addressPrefix (base offset : Mov.Register) (s : State) : State :=
  let s2 := offsetGuardResult offset s
  let s3 := readOpResult (Four.slot base).val (.assign pointerLabel) s2
  let s4 := readOpResult (Four.slot offset).val (.add pointerLabel) s3
  readOpResult 21 (.assign candidateField) s4

@[expose] def addressResult (base offset : Mov.Register) (s : State) : State :=
  guardInvocationResult false (addressPrefix base offset s)

structure AddressPrefixSpec (source : Mov.State) (base offset : Mov.Register) (start finish : State) : Prop where
  executed : Executes 133 start finish
  static : Static finish
  represented : Virtual.Rep dataLayout source finish
  pc : finish.pc = start.pc + 19
  pointer : finish.memory pointerLabel = encodeWord dataLayout.data (source.registers base) +
    encodeWord dataLayout.data (source.registers offset)
  candidate : finish.memory candidateField = encodeWord dataLayout.data (source.registers base) +
    encodeWord dataLayout.data (source.registers offset)

/-- The first tag guard has returned before base/offset addition. All source
registers and heap fields are preserved, so source-register aliasing is allowed. -/
theorem address_prefix_correct (source : Mov.State) (base offset : Mov.Register) (s : State)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (site : LinearAt image s.pc (addressProgram base offset))
    (offsetValid : encodeWord dataLayout.data (source.registers offset) < 13) :
    AddressPrefixSpec source base offset s (addressPrefix base offset s) := by
  have sites := address_sites base offset s.pc site
  let s2 := offsetGuardResult offset s
  let s3 := readOpResult (Four.slot base).val (.assign pointerLabel) s2
  let s4 := readOpResult (Four.slot offset).val (.add pointerLabel) s3
  let s5 := readOpResult 21 (.assign candidateField) s4
  have initial := offset_guard_correct source offset s ready rep sites.1 sites.2.1
  have r2 : Static s2 := initial.static
  have rep2 : Virtual.Rep dataLayout source s2 := initial.represented
  have p2 : s2.pc = s.pc + 7 := by simpa only [offsetValid, ite_true] using initial.pc
  have r3 : Static s3 := read_op_metadata_static _ _ s2 22 r2 (by decide) rfl
  have rep3 : Virtual.Rep dataLayout source s3 := read_op_metadata_source source _ _ s2 22 rep2 rfl
  have p3 : s3.pc = s.pc + 11 := by simp [s3, read_op_pc, p2, Int.add_assoc]
  have v3 : s3.memory pointerLabel = encodeWord dataLayout.data (source.registers base) := by
    rw [show s3 = readOpResult (Four.slot base).val (.assign pointerLabel) s2 by rfl, read_op_assign_value]
    exact register_reader_value source s2 base r2 rep2
  have r4 : Static s4 := read_op_metadata_static _ _ s3 22 r3 (by decide) rfl
  have rep4 : Virtual.Rep dataLayout source s4 := read_op_metadata_source source _ _ s3 22 rep3 rfl
  have p4 : s4.pc = s.pc + 15 := by simp [s4, read_op_pc, p3, Int.add_assoc]
  have v4 : s4.memory pointerLabel = encodeWord dataLayout.data (source.registers base) +
      encodeWord dataLayout.data (source.registers offset) := by
    rw [show s4 = readOpResult (Four.slot offset).val (.add pointerLabel) s3 by rfl,
      read_op_add_value _ s3 pointerLabel (by decide), v3, register_reader_value source s3 offset r3 rep3]
  have r5 : Static s5 := read_op_metadata_static _ _ s4 27 r4 (by decide) rfl
  have rep5 : Virtual.Rep dataLayout source s5 := read_op_metadata_source source _ _ s4 27 rep4 rfl
  have p5 : s5.pc = s.pc + 19 := by simp [s5, read_op_pc, p4, Int.add_assoc]
  have v5 : s5.memory candidateField = encodeWord dataLayout.data (source.registers base) +
      encodeWord dataLayout.data (source.registers offset) := by
    rw [show s5 = readOpResult 21 (.assign candidateField) s4 by rfl,
      read_op_assign_value, static_pointer_reader s4 r4, v4]
  have pointer5 : s5.memory pointerLabel = encodeWord dataLayout.data (source.registers base) +
      encodeWord dataLayout.data (source.registers offset) := by
    rw [show s5 = readOpResult 21 (.assign candidateField) s4 by rfl,
      read_op_memory_frame 21 (.assign candidateField) s4 pointerLabel (by decide) (by decide), v4]
  have e3 : Executes 11 s2 s3 := read_op_correct s2 _ _ r2 (by have := (Four.slot base).isLt; omega)
    (by rw [p2]; exact sites.2.2.1) (meta_is_code 22 (by decide))
  have e4 : Executes 11 s3 s4 := read_op_correct s3 _ _ r3 (by have := (Four.slot offset).isLt; omega)
    (by rw [p3]; exact sites.2.2.2.1) (meta_is_code 22 (by decide))
  have e5 : Executes 11 s4 s5 := read_op_correct s4 21 _ r4 (by decide)
    (by rw [p4]; exact sites.2.2.2.2.1) (meta_is_code 27 (by decide))
  exact ⟨((initial.executed.trans e3).trans e4).trans e5, r5, rep5, p5, pointer5, v5⟩

theorem valid_address_tests (source : Mov.State) (base offset : Mov.Register) (p : Nat × Bool)
    (valid : Mov.address source base offset = some p) :
    encodeWord dataLayout.data (source.registers offset) < 13 ∧
    13 ≤ encodeWord dataLayout.data (source.registers base) + encodeWord dataLayout.data (source.registers offset) := by
  have noFailure : ¬ (13 ≤ encodeWord dataLayout.data (source.registers offset) ∨
      encodeWord dataLayout.data (source.registers base) + encodeWord dataLayout.data (source.registers offset) < 13) := by
    intro failed
    have none := (mov_address_two_concrete_tests source base offset).mpr failed
    rw [valid] at none
    cases none
  exact ⟨by omega, by omega⟩

structure AddressSpec (source : Mov.State) (p : Nat × Bool) (start finish : State) : Prop where
  executed : Executes 222 start finish
  static : Static finish
  represented : Virtual.Rep dataLayout source finish
  pc : finish.pc = start.pc + 22
  pointer : finish.memory pointerLabel = heapField dataLayout.data p

/-- Both tag tests have passed before the dynamic pointer is dereferenced. -/
theorem address_success (source : Mov.State) (base offset : Mov.Register) (p : Nat × Bool) (s : State)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (site : LinearAt image s.pc (addressProgram base offset)) (valid : Mov.address source base offset = some p) :
    AddressSpec source p s (addressResult base offset s) := by
  have tests := valid_address_tests source base offset p valid
  have prepared := address_prefix_correct source base offset s ready rep site tests.1
  have sites := address_sites base offset s.pc site
  have finalCall := guard_invocation_execute false (addressPrefix base offset s) prepared.static
    (by rw [prepared.pc]; exact sites.2.2.2.2.2)
  refine ⟨prepared.executed.trans finalCall.1, finalCall.2,
    guard_invocation_source source false _ prepared.static prepared.represented, ?_, ?_⟩
  · rw [addressResult, guard_invocation_pc false _ prepared.static, prepared.candidate, prepared.pc]
    have passed : ¬ encodeWord dataLayout.data (source.registers base) +
        encodeWord dataLayout.data (source.registers offset) < 13 := by omega
    simp [passed, Int.add_assoc]
  · rw [addressResult, guard_pointer_frame false _ prepared.static, prepared.pointer,
      valid_address_pointer source base offset p valid]

structure AddressFaultSpec (source : Mov.State) (start finish : State) (count : Nat) : Prop where
  positive : 0 < count
  bounded : count ≤ 222
  executed : Executes count start finish
  static : Static finish
  represented : Virtual.Rep dataLayout source finish
  terminal : finish.pc = terminalPC

/-- Invalid offset tags terminate after 100 instructions; invalid bases with
valid offset tags terminate after 222. No invalid dynamic read/store is executed. -/
theorem address_fault (source : Mov.State) (base offset : Mov.Register) (s : State)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (site : LinearAt image s.pc (addressProgram base offset)) (invalid : Mov.address source base offset = none) :
    ∃ count finish, AddressFaultSpec source s finish count := by
  have sites := address_sites base offset s.pc site
  have failed := (mov_address_two_concrete_tests source base offset).mp invalid
  by_cases high : 13 ≤ encodeWord dataLayout.data (source.registers offset)
  · have guarded := offset_guard_correct source offset s ready rep sites.1 sites.2.1
    refine ⟨100, offsetGuardResult offset s, by decide, by decide, guarded.executed, guarded.static,
      guarded.represented, ?_⟩
    have noReturn : ¬ encodeWord dataLayout.data (source.registers offset) < 13 := by omega
    simpa only [noReturn, ite_false] using guarded.pc
  · have low : encodeWord dataLayout.data (source.registers offset) < 13 := by omega
    have baseLow : encodeWord dataLayout.data (source.registers base) +
        encodeWord dataLayout.data (source.registers offset) < 13 := by omega
    have prepared := address_prefix_correct source base offset s ready rep site low
    have finalCall := guard_invocation_execute false (addressPrefix base offset s) prepared.static
      (by rw [prepared.pc]; exact sites.2.2.2.2.2)
    refine ⟨222, addressResult base offset s, by decide, by decide, prepared.executed.trans finalCall.1,
      finalCall.2, guard_invocation_source source false _ prepared.static prepared.represented, ?_⟩
    rw [addressResult, guard_invocation_pc false _ prepared.static, prepared.candidate]
    simp [baseLow]

end SmcTuring.SMC.Concrete

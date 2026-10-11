module
public import SmcTuring.SMC.ConcreteGuardCalls

public section

namespace SmcTuring.SMC.Concrete

open Dolan

theorem static_register_reader (s : State) (r : Mov.Register) (ready : Static s) :
    s.memory (readerLabel (Four.slot r).val) = Virtual.registerField dataLayout r := by
  have bounded := (Four.slot r).isLt
  rw [static_reader_label s _ ready (by omega)]
  simp [metadataValue, bounded, Virtual.registerField, fieldAddress, dataLayout]

theorem register_reader_value (source : Mov.State) (s : State) (r : Mov.Register)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s) :
    s.memory (s.memory (readerLabel (Four.slot r).val)) = encodeWord dataLayout.data (source.registers r) := by
  rw [static_register_reader s r ready]
  exact rep.1 r

theorem read_op_metadata_static (reader : Nat) (operation : Operation) (s : State) (index : Nat)
    (ready : Static s) (dynamic : ¬ StaticSlot index) (destination : operation.field = metaField index) :
    Static (readOpResult reader operation s) := by
  apply read_op_static_frame reader operation s ready
  intro other stable same
  rw [destination] at same
  exact dynamic (metadata_field_injective same ▸ stable)

theorem read_op_metadata_source (source : Mov.State) (reader : Nat) (operation : Operation) (s : State) (index : Nat)
    (rep : Virtual.Rep dataLayout source s) (destination : operation.field = metaField index) :
    Virtual.Rep dataLayout source (readOpResult reader operation s) := by
  apply read_op_source_frame source reader operation s rep
  rw [destination]
  exact metadata_outside_data index

theorem read_op_assign_value (reader : Nat) (s : State) (field : Int) :
    (readOpResult reader (.assign field) s).memory field = s.memory (s.memory (readerLabel reader)) := by
  simp [readOpResult, readInvocationResult, Operation.header, decode, Address.eval, execute]

theorem read_op_add_value (reader : Nat) (s : State) (field : Int) (separate : field ≠ returnField) :
    (readOpResult reader (.add field) s).memory field = s.memory field + s.memory (s.memory (readerLabel reader)) := by
  simp [readOpResult, readInvocationResult, Operation.header, decode, execute, write, separate]

theorem guard_candidate_frame (sense : Bool) (s : State) (ready : Static s) :
    (guardInvocationResult sense s).memory candidateField = s.memory candidateField :=
  guard_invocation_memory_frame sense s ready candidateField (by decide) (by decide) (by decide) (by decide) (by decide)

theorem guard_pointer_frame (sense : Bool) (s : State) (ready : Static s) :
    (guardInvocationResult sense s).memory pointerLabel = s.memory pointerLabel :=
  guard_invocation_memory_frame sense s ready pointerLabel (by decide) (by decide) (by decide) (by decide) (by decide)

theorem read_op_length (reader : Nat) (header : Header) : (readOp reader header).length = 4 := rfl
theorem call_program_length (target : Address) : (callProgram target).length = 3 := rfl
theorem address_program_length (base offset : Mov.Register) : (addressProgram base offset).length = 22 := rfl

theorem address_sites (base offset : Mov.Register) (pc : Int) (site : LinearAt image pc (addressProgram base offset)) :
    LinearAt image pc (readOp (Four.slot offset).val (.store (.fixed candidateField))) ∧
    LinearAt image (pc + 4) (callProgram (.fixed (guardPC true))) ∧
    LinearAt image (pc + 7) (readOp (Four.slot base).val (.store (.fixed pointerLabel))) ∧
    LinearAt image (pc + 11) (readOp (Four.slot offset).val (.add pointerLabel)) ∧
    LinearAt image (pc + 15) (readOp 21 (.store (.fixed candidateField))) ∧
    LinearAt image (pc + 19) (callProgram (.fixed (guardPC false))) := by
  simpa [addressProgram, linear_at_append, read_op_length, call_program_length, Int.add_assoc] using site

theorem mov_address_two_concrete_tests (source : Mov.State) (base offset : Mov.Register) :
    Mov.address source base offset = none ↔
      13 ≤ encodeWord dataLayout.data (source.registers offset) ∨
      encodeWord dataLayout.data (source.registers base) + encodeWord dataLayout.data (source.registers offset) < 13 := by
  have tests := Virtual.mov_address_two_tests dataLayout.data source base offset
  simpa [dataLayout, heapBase, fieldAddress] using tests

theorem valid_address_pointer (source : Mov.State) (base offset : Mov.Register) (p : Nat × Bool)
    (valid : Mov.address source base offset = some p) :
    encodeWord dataLayout.data (source.registers base) + encodeWord dataLayout.data (source.registers offset) =
      heapField dataLayout.data p := by
  cases hb : source.registers base with
  | address cell =>
    cases ho : source.registers offset with
    | address other => simp [Mov.address, hb, ho] at valid
    | offset choice =>
      have same : (cell, choice) = p := Option.some.inj (by simpa [Mov.address, hb, ho] using valid)
      rw [← same, indexed_address_correct]
  | offset choice => cases ho : source.registers offset <;> simp [Mov.address, hb, ho] at valid

theorem static_pointer_reader (s : State) (ready : Static s) : s.memory (readerLabel 21) = pointerLabel := by
  simpa [metadataValue] using static_reader_label s 21 ready (by decide)

theorem guard_invocation_static (sense : Bool) (s : State) (ready : Static s) : Static (guardInvocationResult sense s) :=
  (guard_execute sense (guardEntryResult sense s) (guard_entry_static sense s ready)
    (by rw [guard_entry_effect sense s ready])).2

end SmcTuring.SMC.Concrete

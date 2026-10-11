module
public import SmcTuring.SMC.ConcreteCalls

public section

namespace SmcTuring.SMC.Concrete

open Dolan

/-- Every operation in the shared guard has a memory destination. -/
inductive Operation where
  | assign (field : Int)
  | add (field : Int)
  | subtract (field : Int)
  | bitXor (field : Int)
  | bitAnd (field : Int)
  deriving DecidableEq

@[expose] def Operation.field : Operation → Int
  | .assign field | .add field | .subtract field | .bitXor field | .bitAnd field => field

@[expose] def Operation.header : Operation → Header
  | .assign field => .store (.fixed field)
  | .add field => .add field
  | .subtract field => .subtract field
  | .bitXor field => .bitXor field
  | .bitAnd field => .bitAnd field

@[expose] def readOpResult (reader : Nat) (operation : Operation) (s : State) : State :=
  let read := readInvocationResult (readerLabel reader) (readerPC reader) returnField s
  execute 1 (decode operation.header read) (s.pc + 4) read

theorem operation_writes (operation : Operation) (s : State) (code : image.codeField operation.field) :
    WritesCode image.codeField 1 (decode operation.header s) s := by
  cases operation <;> simpa [Operation.header, Operation.field, WritesCode, footprint, decode, Address.eval] using code

theorem operation_static_frame (operation : Operation) (s : State) (next : Int) (ready : Static s)
    (separate : ∀ index, StaticSlot index → metaField index ≠ operation.field) :
    Static (execute 1 (decode operation.header s) next s) := by
  cases operation with
  | assign field => exact static_write_frame s field s.acc ready separate
  | add field => exact static_write_frame s field (s.memory field + s.acc) ready separate
  | subtract field => exact static_write_frame s field (s.memory field - s.acc) ready separate
  | bitXor field => exact static_write_frame s field (xorWord (s.memory field) s.acc) ready separate
  | bitAnd field => exact static_write_frame s field (andWord (s.memory field) s.acc) ready separate

theorem read_op_static_frame (reader : Nat) (operation : Operation) (s : State) (ready : Static s)
    (separate : ∀ index, StaticSlot index → metaField index ≠ operation.field) :
    Static (readOpResult reader operation s) :=
  operation_static_frame operation _ (s.pc + 4) (read_static_frame s reader ready) separate

theorem read_op_correct (s : State) (reader : Nat) (operation : Operation) (ready : Static s) (bounded : reader < 22)
    (site : LinearAt image s.pc (readOp reader operation.header))
    (code : image.codeField operation.field) :
    runImage 1 image 11 s = some (readOpResult reader operation s) ∧ PureSteps 1 image 11 s := by
  have firstSite : LinearAt image s.pc (callProgram (.fixed (readerPC reader))) :=
    ⟨site.1, site.2.1, site.2.2.1, trivial⟩
  have readyCall := static_call_ready s reader ready bounded firstSite
  have following : image.headers (s.pc + 3) = some (operation.header, s.pc + 4) := by
    simpa [Int.add_assoc] using site.2.2.2.1
  exact read_then_instruction 1 image (readerLabel reader) (readerPC reader) topField returnField s
    readyCall.placed readyCall.entryReset readyCall.entryCall readyCall.top readyCall.constantSeparate
    readyCall.labelSeparate readyCall.targetSeparate readyCall.constantCode readyCall.returnCode readyCall.labelCode
    readyCall.targetCode operation.header (s.pc + 4) following (operation_writes operation _ code)

theorem read_op_pc (reader : Nat) (operation : Operation) (s : State) : (readOpResult reader operation s).pc = s.pc + 4 := by
  cases operation <;> rfl

theorem read_op_acc (reader : Nat) (operation : Operation) (s : State) :
    (readOpResult reader operation s).acc = s.memory (s.memory (readerLabel reader)) := by
  cases operation <;> rfl

theorem read_op_memory_frame (reader : Nat) (operation : Operation) (s : State) (field : Int)
    (returnSeparate : field ≠ returnField) (destinationSeparate : field ≠ operation.field) :
    (readOpResult reader operation s).memory field = s.memory field := by
  cases operation <;> simp_all [readOpResult, Operation.header, Operation.field, execute, decode,
    Address.eval, readInvocationResult, write]

theorem read_op_source_frame (source : Mov.State) (reader : Nat) (operation : Operation) (s : State)
    (rep : Virtual.Rep dataLayout source s) (outside : ¬ codeField dataLayout.data operation.field) :
    Virtual.Rep dataLayout source (readOpResult reader operation s) := by
  constructor
  · intro r
    rw [read_op_memory_frame reader operation s (Virtual.registerField dataLayout r)
      (data_field_separate dataLayout.data _ _ (metadata_outside_data 26) (Virtual.register_is_code dataLayout r))
      (data_field_separate dataLayout.data _ _ outside (Virtual.register_is_code dataLayout r))]
    exact rep.1 r
  · intro p
    rw [read_op_memory_frame reader operation s (heapField dataLayout.data p)
      (data_field_separate dataLayout.data _ _ (metadata_outside_data 26) (heap_is_code dataLayout.data p))
      (data_field_separate dataLayout.data _ _ outside (heap_is_code dataLayout.data p))]
    exact rep.2 p

end SmcTuring.SMC.Concrete

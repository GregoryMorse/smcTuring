module
public import SmcTuring.Defaddr
public import SmcTuring.SMC.Words

public section

namespace SmcTuring.SMC

/-- Unbounded integer words. Native 32/64-bit refinement is conditional on
representability; this model does not identify infinite addresses with uint64. -/
structure State where
  acc : Int
  stack : Int
  pc : Int
  carry : Bool
  memory : Int → Int

inductive Address where
  | fixed (value : Int)
  | accumulator
  | operand (field : Int)
  deriving DecidableEq, Repr

@[expose] def Address.eval (a : Address) (s : State) : Int :=
  match a with
  | .fixed value => value
  | .accumulator => s.acc
  | .operand field => s.memory field

/-- These are the memory-writing forms used by the proposed lowering.
Arithmetic destinations are memory, and MOV sources are accumulator or SP.
The CALL's return-address write is modeled explicitly. -/
inductive Header where
  | exchange (address : Address)
  | store (address : Address)
  | add (field : Int)
  | subtract (field : Int)
  | subtractBorrowZero (field : Int)
  | bitXor (field : Int)
  | bitAnd (field : Int)
  | exchangeStack (field : Int)
  | storeStack (field : Int)
  | call (target : Address)
  deriving DecidableEq, Repr

/-- Fetch resolves mutable encoded address operands in the current memory.
Negative scratch values remain valid words; address validity is a separate
layout/refinement obligation. -/
inductive Instruction where
  | exchange (destination : Int)
  | store (destination : Int)
  | add (field : Int)
  | subtract (field : Int)
  | subtractBorrowZero (field : Int)
  | bitXor (field : Int)
  | bitAnd (field : Int)
  | exchangeStack (field : Int)
  | storeStack (field : Int)
  | call (target : Int)
  deriving DecidableEq, Repr

@[expose] def decode (header : Header) (s : State) : Instruction :=
  match header with
  | .exchange a => .exchange (a.eval s)
  | .store a => .store (a.eval s)
  | .add field => .add field
  | .subtract field => .subtract field
  | .subtractBorrowZero field => .subtractBorrowZero field
  | .bitXor field => .bitXor field
  | .bitAnd field => .bitAnd field
  | .exchangeStack field => .exchangeStack field
  | .storeStack field => .storeStack field
  | .call a => .call (a.eval s)

@[expose] def borrowWord (carry : Bool) : Int := if carry then 1 else 0

/-- Integer arithmetic models the unbounded construction. SUB's carry law is
used on nonnegative addresses; fixed-width modular/flag bridges are separate.
The word size controls the stack pointer's address decrement, not a hidden
bound on the integer words in this abstract model. -/
@[expose] def execute (wordBytes : Int) (i : Instruction) (next : Int) (s : State) : State :=
  match i with
  | .exchange destination =>
    { s with acc := s.memory destination, memory := write s.memory destination s.acc, pc := next }
  | .store destination => { s with memory := write s.memory destination s.acc, pc := next }
  | .add field =>
    { s with memory := write s.memory field (s.memory field + s.acc), carry := false, pc := next }
  | .subtract field =>
    { s with memory := write s.memory field (s.memory field - s.acc)
             carry := decide (s.memory field < s.acc)
             pc := next }
  | .subtractBorrowZero field =>
    { s with memory := write s.memory field (s.memory field - borrowWord s.carry)
             carry := decide (s.memory field < borrowWord s.carry)
             pc := next }
  | .bitXor field =>
    { s with memory := write s.memory field (xorWord (s.memory field) s.acc), carry := false, pc := next }
  | .bitAnd field =>
    { s with memory := write s.memory field (andWord (s.memory field) s.acc), carry := false, pc := next }
  | .exchangeStack field =>
    { s with stack := s.memory field, memory := write s.memory field s.stack, pc := next }
  | .storeStack field => { s with memory := write s.memory field s.stack, pc := next }
  | .call target =>
    { s with stack := s.stack - wordBytes, memory := write s.memory (s.stack - wordBytes) next, pc := target }

/-- A write event is recorded even when it stores the existing value. -/
@[expose] def footprint (wordBytes : Int) (i : Instruction) (s : State) : List Int :=
  match i with
  | .exchange field | .store field | .add field | .subtract field | .subtractBorrowZero field
  | .bitXor field | .bitAnd field | .exchangeStack field | .storeStack field => [field]
  | .call _ => [s.stack - wordBytes]

theorem every_instruction_writes (wordBytes : Int) (i : Instruction) (s : State) :
    footprint wordBytes i s ≠ [] := by cases i <;> simp [footprint]

theorem execute_memory_frame (wordBytes : Int) (i : Instruction) (next : Int) (s : State) (p : Int)
    (separate : p ∉ footprint wordBytes i s) : (execute wordBytes i next s).memory p = s.memory p := by
  cases i <;> simp_all [execute, footprint, write]

@[expose] def WritesCode (codeField : Int → Prop) (wordBytes : Int) (i : Instruction) (s : State) : Prop :=
  footprint wordBytes i s ≠ [] ∧ ∀ p ∈ footprint wordBytes i s, codeField p

/-- A storage template has its own mutable operand. The field must belong to
such a template, rather than being ordinary data on an executable page. -/
structure Image where
  headers : Int → Option (Header × Int)
  templatePC : Int → Int
  codeField : Int → Prop
  storageTemplate : ∀ field, codeField field →
    ∃ next, headers (templatePC field) = some (.store (.operand field), next)

@[expose] def fetch (image : Image) (s : State) : Option (Instruction × Int) :=
  (image.headers s.pc).map (fun entry => (decode entry.1 s, entry.2))

@[expose] def step (wordBytes : Int) (image : Image) (s : State) : Option State :=
  (fetch image s).map (fun entry => execute wordBytes entry.1 entry.2 s)

theorem fetch_storage_current_word (image : Image) (s : State) (field : Int)
    (code : image.codeField field) (here : s.pc = image.templatePC field) :
    ∃ next, fetch image s = some (.store (s.memory field), next) := by
  rcases image.storageTemplate field code with ⟨next, header⟩
  exact ⟨next, by simp [fetch, here, header, decode, Address.eval]⟩

theorem patched_operand_changes_fetch (image : Image) (s : State) (field value next : Int)
    (header : image.headers (image.templatePC field) = some (.store (.operand field), next))
    (here : s.pc = image.templatePC field) :
    fetch image { s with memory := write s.memory field value } = some (.store value, next) := by
  simp [fetch, here, header, decode, Address.eval, write]

@[expose] def run (wordBytes : Int) : List Header → State → State
  | [], s => s
  | header :: rest, s => run wordBytes rest (execute wordBytes (decode header s) (s.pc + 1) s)

theorem run_append (wordBytes : Int) (first second : List Header) (s : State) :
    run wordBytes (first ++ second) s = run wordBytes second (run wordBytes first s) := by
  induction first generalizing s with
  | nil => rfl
  | cons header rest ih => simp [run, ih]

@[expose] def PureRun (codeField : Int → Prop) (wordBytes : Int) : List Header → State → Prop
  | [], _ => True
  | header :: rest, s => WritesCode codeField wordBytes (decode header s) s ∧
      PureRun codeField wordBytes rest (execute wordBytes (decode header s) (s.pc + 1) s)

theorem pure_append (codeField : Int → Prop) (wordBytes : Int) (first second : List Header) (s : State) :
    PureRun codeField wordBytes (first ++ second) s ↔
      PureRun codeField wordBytes first s ∧ PureRun codeField wordBytes second (run wordBytes first s) := by
  induction first generalizing s with
  | nil => simp [PureRun, run]
  | cons header rest ih => simp [PureRun, run, ih, and_assoc]

end SmcTuring.SMC

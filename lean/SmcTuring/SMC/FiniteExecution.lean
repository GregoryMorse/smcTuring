module
public import SmcTuring.SMC.Execution

public section

namespace SmcTuring.SMC.Finite

/-- A finite execution description. The initial word generator is fixed by the
finite program/input, while all subsequent writes are stored newest first. -/
structure State where
  acc : Int
  stack : Int
  pc : Int
  carry : Bool
  changes : List (Int × Int)
  deriving Repr, DecidableEq

@[expose] def lookup (initial : Int → Int) : List (Int × Int) → Int → Int
  | [], field => initial field
  | entry :: rest, field => if field = entry.1 then entry.2 else lookup initial rest field

@[expose] def meaning (initial : Int → Int) (s : State) : SMC.State :=
  { acc := s.acc, stack := s.stack, pc := s.pc, carry := s.carry,
    memory := lookup initial s.changes }

theorem lookup_cons (initial : Int → Int) (changes : List (Int × Int)) (field datum : Int) :
    lookup initial ((field, datum) :: changes) = write (lookup initial changes) field datum := rfl

theorem lookup_outside (initial : Int → Int) (changes : List (Int × Int)) (field : Int)
    (untouched : field ∉ changes.map Prod.fst) : lookup initial changes field = initial field := by
  induction changes with
  | nil => rfl
  | cons entry rest ih =>
    have outside : field ≠ entry.1 ∧ field ∉ rest.map Prod.fst := by simpa using untouched
    simp only [lookup, outside.1, ite_false]
    exact ih outside.2

@[expose] def eval (initial : Int → Int) (address : Address) (s : State) : Int :=
  match address with
  | .fixed value => value
  | .accumulator => s.acc
  | .operand field => lookup initial s.changes field

@[expose] def decode (initial : Int → Int) (header : Header) (s : State) : Instruction :=
  match header with
  | .exchange a => .exchange (eval initial a s)
  | .store a => .store (eval initial a s)
  | .add field => .add field
  | .subtract field => .subtract field
  | .subtractBorrowZero field => .subtractBorrowZero field
  | .bitXor field => .bitXor field
  | .bitAnd field => .bitAnd field
  | .exchangeStack field => .exchangeStack field
  | .storeStack field => .storeStack field
  | .call a => .call (eval initial a s)

theorem eval_correct (initial : Int → Int) (address : Address) (s : State) :
    eval initial address s = address.eval (meaning initial s) := by cases address <;> rfl

theorem decode_correct (initial : Int → Int) (header : Header) (s : State) :
    decode initial header s = SMC.decode header (meaning initial s) := by
  cases header <;> simp only [decode, SMC.decode, eval_correct]

/-- An executable list-update algorithm, independently defined from the
function-memory semantics. Each computational instruction appends one record. -/
@[expose] def execute (wordBytes : Int) (initial : Int → Int) (instruction : Instruction)
    (next : Int) (s : State) : State :=
  match instruction with
  | .exchange field =>
    { s with acc := lookup initial s.changes field, pc := next, changes := (field, s.acc) :: s.changes }
  | .store field => { s with pc := next, changes := (field, s.acc) :: s.changes }
  | .add field =>
    { s with pc := next, carry := false, changes := (field, lookup initial s.changes field + s.acc) :: s.changes }
  | .subtract field =>
    { s with
      pc := next
      carry := decide (lookup initial s.changes field < s.acc)
      changes := (field, lookup initial s.changes field - s.acc) :: s.changes }
  | .subtractBorrowZero field =>
    { s with
      pc := next
      carry := decide (lookup initial s.changes field < borrowWord s.carry)
      changes := (field, lookup initial s.changes field - borrowWord s.carry) :: s.changes }
  | .bitXor field =>
    { s with pc := next, carry := false, changes := (field, xorWord (lookup initial s.changes field) s.acc) :: s.changes }
  | .bitAnd field =>
    { s with pc := next, carry := false, changes := (field, andWord (lookup initial s.changes field) s.acc) :: s.changes }
  | .exchangeStack field =>
    { s with stack := lookup initial s.changes field, pc := next, changes := (field, s.stack) :: s.changes }
  | .storeStack field => { s with pc := next, changes := (field, s.stack) :: s.changes }
  | .call target =>
    { s with stack := s.stack - wordBytes, pc := target, changes := (s.stack - wordBytes, next) :: s.changes }

theorem execute_correct (wordBytes : Int) (initial : Int → Int) (instruction : Instruction) (next : Int) (s : State) :
    meaning initial (execute wordBytes initial instruction next s) = SMC.execute wordBytes instruction next (meaning initial s) := by
  cases instruction <;> rfl

theorem execute_length (wordBytes : Int) (initial : Int → Int) (instruction : Instruction) (next : Int) (s : State) :
    (execute wordBytes initial instruction next s).changes.length = s.changes.length + 1 := by
  cases instruction <;> rfl

@[expose] def step (wordBytes : Int) (headers : Int → Option (Header × Int)) (initial : Int → Int) (s : State) : Option State :=
  (headers s.pc).map fun entry => execute wordBytes initial (decode initial entry.1 s) entry.2 s

theorem step_correct (wordBytes : Int) (image : Image) (initial : Int → Int) (s : State) :
    (step wordBytes image.headers initial s).map (meaning initial) = SMC.step wordBytes image (meaning initial s) := by
  cases fetched : image.headers s.pc with
  | none => simp [step, SMC.step, fetch, meaning, fetched]
  | some entry =>
    rcases entry with ⟨header, next⟩
    have pc : (meaning initial s).pc = s.pc := rfl
    simp only [step, SMC.step, fetch, pc, fetched, Option.map_some]
    rw [execute_correct, decode_correct]

theorem step_length (wordBytes : Int) (headers : Int → Option (Header × Int)) (initial : Int → Int)
    (s finish : State) (completed : step wordBytes headers initial s = some finish) :
    finish.changes.length = s.changes.length + 1 := by
  cases fetched : headers s.pc with
  | none => simp [step, fetched] at completed
  | some entry =>
    have same : execute wordBytes initial (decode initial entry.1 s) entry.2 s = finish :=
      Option.some.inj (by simpa only [step, fetched, Option.map_some] using completed)
    subst finish
    exact execute_length _ _ _ _ _

@[expose] def run (wordBytes : Int) (headers : Int → Option (Header × Int)) (initial : Int → Int) : Nat → State → Option State
  | 0, s => some s
  | count + 1, s => (step wordBytes headers initial s).bind (run wordBytes headers initial count)

/-- Exact finite-prefix correspondence, including failure. No infinite memory
is copied or supplied as a changing input to the finite evaluator. -/
theorem run_correct (wordBytes : Int) (image : Image) (initial : Int → Int) (count : Nat) (s : State) :
    (run wordBytes image.headers initial count s).map (meaning initial) = runImage wordBytes image count (meaning initial s) := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih =>
    simp only [run, runImage, ← step_correct]
    cases first : step wordBytes image.headers initial s with
    | none => simp
    | some middle => simpa only [Option.bind_some, Option.map_some] using ih middle

theorem run_length (wordBytes : Int) (headers : Int → Option (Header × Int)) (initial : Int → Int)
    (count : Nat) (s finish : State) (completed : run wordBytes headers initial count s = some finish) :
    finish.changes.length = s.changes.length + count := by
  induction count generalizing s with
  | zero =>
    have same : s = finish := Option.some.inj completed
    subst finish
    simp
  | succ count ih =>
    cases first : step wordBytes headers initial s with
    | none => simp [run, first] at completed
    | some middle =>
      have tail : run wordBytes headers initial count middle = some finish := by simpa [run, first] using completed
      have before := step_length wordBytes headers initial s middle first
      have after := ih middle tail
      omega

/-- Every reached functional-memory state has a finite list description with
exactly one additional record per executed instruction. -/
theorem reached_description (wordBytes : Int) (image : Image) (initial : Int → Int)
    (count : Nat) (s : State) (finish : SMC.State)
    (completed : runImage wordBytes image count (meaning initial s) = some finish) :
    ∃ description, run wordBytes image.headers initial count s = some description ∧
      meaning initial description = finish ∧ description.changes.length = s.changes.length + count := by
  have correspondence := run_correct wordBytes image initial count s
  rw [completed] at correspondence
  cases actual : run wordBytes image.headers initial count s with
  | none => simp [actual] at correspondence
  | some description =>
    refine ⟨description, rfl, ?_, run_length wordBytes image.headers initial count s description actual⟩
    exact Option.some.inj (by simpa only [actual, Option.map_some] using correspondence)

end SmcTuring.SMC.Finite

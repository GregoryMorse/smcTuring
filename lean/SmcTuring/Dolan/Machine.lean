module
public import SmcTuring.Memory

public section

namespace SmcTuring.Dolan.Mov

/-- A valid cell address is separate from either offset. Native word addresses
are 2*(cell+1) and the indexed word is chosen by a Boolean offset. -/
inductive Word where
  | address (cell : Nat)
  | offset (choice : Bool)
  deriving DecidableEq, Repr

inductive Register where
  | zero | one | transition | current | left | right | scratch
  | x | y | matched | value | direction | halted
  deriving DecidableEq, Repr

/-- Exactly the three addressing forms in Dolan's machine model. -/
inductive Instruction where
  | immediate (dest : Register) (value : Word)
  | load (dest base offset : Register)
  | store (base offset source : Register)
  deriving DecidableEq, Repr

abbrev Memory := Nat × Bool → Word

structure State where
  registers : Register → Word
  memory : Memory

@[expose] def address (s : State) (base offset : Register) : Option (Nat × Bool) :=
  match s.registers base, s.registers offset with
  | .address cell, .offset choice => some (cell, choice)
  | _, _ => none

/-- An invalid dereference (including treating offset zero as an address) traps. -/
@[expose] def execute (i : Instruction) (s : State) : Option State :=
  match i with
  | .immediate dest value => some { s with registers := write s.registers dest value }
  | .load dest base offset =>
    match address s base offset with
    | none => none
    | some p => some { s with registers := write s.registers dest (s.memory p) }
  | .store base offset source =>
    match address s base offset with
    | none => none
    | some p => some { s with memory := write s.memory p (s.registers source) }

@[expose] def run : List Instruction → State → Option State
  | [], s => some s
  | i :: rest, s => (execute i s).bind (run rest)

theorem run_append (first second : List Instruction) (s : State) :
    run (first ++ second) s = (run first s).bind (run second) := by
  induction first generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.cons_append, run]
    cases h : execute i s <;> simp [ih]

/-- Compose two completed blocks without unfolding their instruction lists. -/
theorem run_composition {first second : List Instruction} {start middle finish : State}
    (hfirst : run first start = some middle) (hsecond : run second middle = some finish) :
    run (first ++ second) start = some finish := by
  calc
    _ = (run first start).bind (run second) := run_append first second start
    _ = (some middle).bind (run second) :=
      congrArg (fun result : Option State => result.bind (run second)) hfirst
    _ = some finish := hsecond

theorem load_correct (s : State) (dest base offset : Register)
    (cell : Nat) (choice : Bool)
    (hb : s.registers base = .address cell) (ho : s.registers offset = .offset choice) :
    execute (.load dest base offset) s =
      some { s with registers := write s.registers dest (s.memory (cell, choice)) } := by
  simp [execute, address, hb, ho]

theorem store_correct (s : State) (base offset source : Register)
    (cell : Nat) (choice : Bool)
    (hb : s.registers base = .address cell) (ho : s.registers offset = .offset choice) :
    execute (.store base offset source) s =
      some { s with memory := write s.memory (cell, choice) (s.registers source) } := by
  simp [execute, address, hb, ho]

/-- The invalid-zero load implements the source's chosen halt observation. -/
theorem offset_dereference_traps (s : State) (dest base offset : Register)
    (value : Bool) (hb : s.registers base = .offset value) :
    execute (.load dest base offset) s = none := by
  simp [execute, address, hb]

/-- The program is static: only data memory and registers are updated. Its sole
back-edge is represented explicitly by restarting the same list after each pass. -/
inductive Passes (program : List Instruction) : State → State → Nat → Prop where
  | zero (s : State) : Passes program s s 0
  | succ {s middle finish : State} {n : Nat}
      (first : run program s = some middle)
      (rest : Passes program middle finish n) : Passes program s finish (n + 1)

end SmcTuring.Dolan.Mov

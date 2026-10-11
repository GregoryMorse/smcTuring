module
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public section
/-!
# Corrected Morse/Dolan principal mathematical result
The statement selects finite-TM halt/divergence simulation, instruction-level
pure code writes, unbounded fetched-code changes, the four-register MOV
foundation, a finite effective interpreter, and SAME-trace tape/head observations.
Its definitions retain the development's names and exact mathematical meanings.
Gregory Morse (2018), DOI 10.24425/119359, is adapted with proved M01–M20 errata;
Stephen Dolan's 2013 MOV paper supplies the foundation. Mathlib supplies TM0.
Codex assisted development; no independent human review or new novelty is claimed.
The checked conditional native/x86/x64/COFF theorems are supporting material,
outside this selected registry statement. See PALOMAR_AUDIT.md for scope.
All four intentional theorem holes belong to Challenge; Solution proves them.
The four compared result definitions have their intended values here.
No future-run certificate, simulation oracle or custom axiom is assumed.
No submission or registration has been performed.
-/
set_option maxHeartbeats 2000000
namespace SmcTuring
/-- A word-addressed memory update, keeping every other address unchanged. -/
@[expose] def write {α β : Type} [DecidableEq α] (m : α → β) (a : α) (v : β) : α → β := fun x => if x = a then v else m x
end SmcTuring
namespace SmcTuring.TM
/-- A standard finite-alphabet, finite-state, two-sided Turing machine.
Each transition writes one symbol, moves one place, and chooses a new state.
None means halt. The finite indices supply effective enumerations. -/
structure Machine (alphabet states : Nat) where
  blank : Fin alphabet
  start : Fin states
  transition : Fin states → Fin alphabet → Option (Fin alphabet × Bool × Fin states)
structure Configuration (alphabet states : Nat) where
  state : Fin states
  head : Int
  tape : Int → Fin alphabet
@[expose] def step {alphabet states : Nat} (machine : Machine alphabet states) (c : Configuration alphabet states) : Option (Configuration alphabet states) := match machine.transition c.state (c.tape c.head) with
  | none => none
  | some (symbol, right, state) =>
    some { state := state
           head := if right then c.head + 1 else c.head - 1
           tape := write c.tape c.head symbol }
/-- A finite input is placed to the right of head zero; all other cells are blank. -/
@[expose] def initialConfiguration {alphabet states : Nat} (machine : Machine alphabet states) (input : List (Fin alphabet)) : Configuration alphabet states :=
  { state := machine.start
    head := 0
    tape := fun position => if position < 0 then machine.blank
            else (input[position.toNat]?).getD machine.blank }
@[expose] def run {alphabet states : Nat} (machine : Machine alphabet states) : Nat → Configuration alphabet states → Option (Configuration alphabet states)
  | 0, c => some c
  | n + 1, c => (step machine c).bind (run machine n)
/-- Halting is a missing transition reached after finitely many actual steps. -/
@[expose] def Halts {alphabet states : Nat} (machine : Machine alphabet states) (start : Configuration alphabet states) : Prop := ∃ n finish, run machine n start = some finish ∧ step machine finish = none
/-- Infinite computation is defined through every finite prefix, not by
selecting a separate finite-memory hardware instance for each prefix. -/
@[expose] def Diverges {alphabet states : Nat} (machine : Machine alphabet states) (start : Configuration alphabet states) : Prop := ∀ n, ∃ finish, run machine n start = some finish
end SmcTuring.TM
namespace SmcTuring.TM
/-- A TM's entire external input is finite data, with no transition function
oracle. Short or absent rows denote missing transitions. -/
structure FrozenMachine (alphabet states : Nat) where
  blank : Fin alphabet
  start : Fin states
  table : List (List (Option (Fin alphabet × Bool × Fin states)))
@[expose] def thaw {alphabet states : Nat} (machine : FrozenMachine alphabet states) : Machine alphabet states :=
  { blank := machine.blank, start := machine.start,
    transition := fun state symbol => (((machine.table[state.val]?).getD [])[symbol.val]?).getD none }
end SmcTuring.TM
namespace SmcTuring.SMC
/-- Two's-complement integer XOR, with each negative integer represented as
the complement of a natural number. Finite-width refinement is separate. -/
@[expose] def xorWord : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)
/-- Integer AND. For a nonnegative operand, XOR removes precisely the bits
selected by the other operand when that operand is complemented. -/
@[expose] def andWord : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a &&& b)
  | .ofNat a, .negSucc b => .ofNat (a ^^^ (a &&& b))
  | .negSucc a, .ofNat b => .ofNat (b ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)
end SmcTuring.SMC
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
@[expose] def Address.eval (a : Address) (s : State) : Int := match a with
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
@[expose] def decode (header : Header) (s : State) : Instruction := match header with
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
@[expose] def execute (wordBytes : Int) (i : Instruction) (next : Int) (s : State) : State := match i with
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
@[expose] def footprint (wordBytes : Int) (i : Instruction) (s : State) : List Int := match i with
  | .exchange field | .store field | .add field | .subtract field | .subtractBorrowZero field
  | .bitXor field | .bitAnd field | .exchangeStack field | .storeStack field => [field]
  | .call _ => [s.stack - wordBytes]
@[expose] def WritesCode (codeField : Int → Prop) (wordBytes : Int) (i : Instruction) (s : State) : Prop := footprint wordBytes i s ≠ [] ∧ ∀ p ∈ footprint wordBytes i s, codeField p
/-- A storage template has its own mutable operand. The field must belong to
such a template, rather than being ordinary data on an executable page. -/
structure Image where
  headers : Int → Option (Header × Int)
  templatePC : Int → Int
  codeField : Int → Prop
  storageTemplate : ∀ field, codeField field →
    ∃ next, headers (templatePC field) = some (.store (.operand field), next)
@[expose] def fetch (image : Image) (s : State) : Option (Instruction × Int) := (image.headers s.pc).map (fun entry => (decode entry.1 s, entry.2))
@[expose] def step (wordBytes : Int) (image : Image) (s : State) : Option State := (fetch image s).map (fun entry => execute wordBytes entry.1 entry.2 s)
end SmcTuring.SMC
namespace SmcTuring.SMC
@[expose] def readProgram (label : Int) : List Header := [.exchange (.fixed label), .store (.fixed label), .exchange .accumulator, .store (.operand label)]
@[expose] def stackResetProgram (field : Int) : List Header := [.exchangeStack field, .storeStack field]
end SmcTuring.SMC
namespace SmcTuring.Dolan.Table
structure Entry (alphabet states : Nat) where
  trigger : Fin alphabet
  symbol : Fin alphabet
  direction : Bool
  destination : Fin states
  deriving DecidableEq
/-- The finite list of actual transitions for one state. Undefined transitions
are omitted, so exhausting this list represents a missing TM transition. -/
@[expose] def entries {alphabet states : Nat} (machine : TM.Machine alphabet states) (state : Fin states) : List (Entry alphabet states) := (List.ofFn (fun symbol : Fin alphabet => symbol)).filterMap fun trigger =>
    (machine.transition state trigger).map fun result =>
      { trigger := trigger, symbol := result.1, direction := result.2.1, destination := result.2.2 }
end SmcTuring.Dolan.Table
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
end SmcTuring.Dolan.Mov
namespace SmcTuring.Dolan.Mov
/-- A literal MOV program: initialize the offset registers, store zero at Y,
store one at X, then read Y to obtain the equality flag. -/
@[expose] def comparison : List Instruction := [.immediate .zero (.offset false), .immediate .one (.offset true),
   .store .y .zero .zero, .store .x .zero .one, .load .matched .y .zero]
/-- This three-instruction selector uses only the original indexed store/load forms. -/
@[expose] def selection : List Instruction := [.store .scratch .zero .x, .store .scratch .one .y, .load .value .scratch .matched]
end SmcTuring.Dolan.Mov
namespace SmcTuring.Dolan.Mov
/-- Literal MOV expansion of the paper's conditional push block.
False direction pushes onto the right stack; true pushes onto the left. -/
@[expose] def pushProgram : List Instruction := [.store .scratch .zero .right, .store .scratch .one .left,
   .load .x .scratch .direction, .store .current .one .x,
   .store .scratch .zero .left, .store .scratch .one .current,
   .load .left .scratch .direction,
   .store .scratch .zero .current, .store .scratch .one .right,
   .load .right .scratch .direction]
/-- Literal MOV expansion of the corrected pop block. The preserved left
register is L, as required by the two-stack invariant. -/
@[expose] def popProgram : List Instruction := [.store .scratch .zero .left, .store .scratch .one .right,
   .load .current .scratch .direction, .load .x .current .one,
   .store .scratch .zero .x, .store .scratch .one .left,
   .load .left .scratch .direction,
   .store .scratch .zero .right, .store .scratch .one .x,
   .load .right .scratch .direction]
/-- Keep the push direction on a match; otherwise pop in the opposite
direction so the push is undone. All six instructions are MOVs. -/
@[expose] def popDirectionProgram : List Instruction := [.store .scratch .zero .one, .store .scratch .one .zero,
   .load .x .scratch .direction,
   .store .scratch .zero .x, .store .scratch .one .direction,
   .load .direction .scratch .matched]
@[expose] def advanceProgram : List Instruction := pushProgram ++ popDirectionProgram ++ popProgram
end SmcTuring.Dolan.Mov
namespace SmcTuring.Dolan.Encoding
open Mov
/-- Distinct logical tape positions have distinct physical cells. The scratch
cell is separate. Symbols are represented by addresses, as in Dolan's paper. -/
structure Layout (alphabet : Nat) where
  cell : Int → Nat
  symbol : Fin alphabet → Nat
  scratch : Nat
  cell_injective : Function.Injective cell
  cell_scratch : ∀ position, cell position ≠ scratch
/-- The link in the current cell is deliberately unconstrained. All other
links point away from the head, implementing the two persistent stacks. -/
@[expose] def MemoryRep {alphabet states : Nat} (layout : Layout alphabet) (c : TM.Configuration alphabet states) (memory : Memory) : Prop := (∀ position, memory (layout.cell position, false) = .address (layout.symbol (c.tape position))) ∧
  (∀ position, position < c.head →
    memory (layout.cell position, true) = .address (layout.cell (position - 1))) ∧
  (∀ position, c.head < position →
    memory (layout.cell position, true) = .address (layout.cell (position + 1)))
@[expose] def RegistersRep {alphabet states : Nat} (layout : Layout alphabet) (c : TM.Configuration alphabet states) (registers : Register → Word) : Prop := registers .current = .address (layout.cell c.head) ∧
  registers .left = .address (layout.cell (c.head - 1)) ∧
  registers .right = .address (layout.cell (c.head + 1))
@[expose] def TapeRep {alphabet states : Nat} (layout : Layout alphabet) (c : TM.Configuration alphabet states) (s : State) : Prop := RegistersRep layout c s.registers ∧ MemoryRep layout c s.memory
end SmcTuring.Dolan.Encoding
namespace SmcTuring.Dolan.Encoding
open Mov
/-- A computable bijective enumeration of the two-sided tape positions. -/
@[expose] def zigzag : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1
@[expose] def unzigzag (n : Nat) : Int := if n % 2 = 0 then .ofNat (n / 2) else .negSucc (n / 2)
theorem zigzag_injective : Function.Injective zigzag := by sorry
/-- Reserve finitely many low cells for symbols and other simulator data.
Every tape cell is above that finite prefix. -/
@[expose] def standardLayout (alphabet reserved : Nat) : Layout alphabet where
  cell position := alphabet + reserved + 1 + zigzag position
  symbol symbol := symbol.val + 1
  scratch := 0
  cell_injective := by
    intro a b h
    dsimp at h
    apply zigzag_injective
    omega
  cell_scratch := by
    intro position
    dsimp
    omega
/-- This is an explicit computable memory function, not an existentially
chosen oracle containing a future computation. The tape is blank except for
the supplied finite input when c is a standard initial configuration. -/
@[expose] def encodedMemory {alphabet states : Nat} (reserved : Nat) (c : TM.Configuration alphabet states) : Memory := fun p =>
  let base := alphabet + reserved + 1
  if p.1 < base then .offset false
  else
    let position := unzigzag (p.1 - base)
    if p.2 then
      .address ((standardLayout alphabet reserved).cell
        (if position < c.head then position - 1 else position + 1))
    else .address ((standardLayout alphabet reserved).symbol (c.tape position))
end SmcTuring.Dolan.Encoding
namespace SmcTuring.Dolan.Table
open Mov Encoding
@[expose] def tableLimit (alphabet states : Nat) : Nat := alphabet + 1 + 5 * (alphabet * states)
/-- Allocate a cursor cell and four body cells for every possible candidate.
Only the candidates in the filtered transition list are used. -/
@[expose] def node {states : Nat} (alphabet : Nat) (state : Fin states) (index : Nat) : Nat := alphabet + 1 + 5 * (index + alphabet * state.val)
@[expose] def cursor {alphabet states : Nat} (machine : TM.Machine alphabet states) (state : Fin states) (index : Nat) : Nat := if index < (entries machine state).length then node alphabet state index else 0
@[expose] def head {alphabet states : Nat} (machine : TM.Machine alphabet states) (state : Fin states) : Nat := cursor machine state 0
/-- The nine used fields follow the linked-cell layout in Dolan's construction.
The tenth field is unused. A destination stores the head of its state's list. -/
@[expose] def recordWord {alphabet states : Nat} (machine : TM.Machine alphabet states) (state : Fin states) (index : Nat) (entry : Entry alphabet states) (component : Nat) (choice : Bool) : Word := match component, choice with
  | 0, false => .address (node alphabet state index + 1)
  | 0, true => .address (cursor machine state (index + 1))
  | 1, false => .address (entry.trigger.val + 1)
  | 1, true => .address (node alphabet state index + 2)
  | 2, false => .address (entry.symbol.val + 1)
  | 2, true => .address (node alphabet state index + 3)
  | 3, false => .offset entry.direction
  | 3, true => .address (node alphabet state index + 4)
  | 4, false => .address (head machine entry.destination)
  | _, _ => .offset false
@[expose] def TableRep {alphabet states : Nat} (machine : TM.Machine alphabet states) (memory : Memory) : Prop := ∀ (state : Fin states) (index : Fin (entries machine state).length)
    (component : Fin 5) (choice : Bool),
    memory (node alphabet state index.val + component.val, choice) =
      recordWord machine state index.val (entries machine state)[index.val] component.val choice
/-- A finite table is decoded by division and remainder; the memory generator
queries the supplied finite transition table, never a future machine run. -/
@[expose] def tableMemory {alphabet states : Nat} (machine : TM.Machine alphabet states) : Memory := fun p =>
    if p.1 < alphabet + 1 then .offset false else
      let relative := p.1 - (alphabet + 1)
      let row := relative / 5
      let stateIndex := row / alphabet
      let candidate := row % alphabet
      if h : stateIndex < states then
        let state : Fin states := ⟨stateIndex, h⟩
        match (entries machine state)[candidate]? with
        | none => .offset false
        | some entry => recordWord machine state candidate entry (relative % 5) p.2
      else .offset false
@[expose] def tapeLayout (alphabet states : Nat) : Layout alphabet := standardLayout alphabet (5 * (alphabet * states))
@[expose] def initialMemory {alphabet states : Nat} (machine : TM.Machine alphabet states) (c : TM.Configuration alphabet states) : Memory := fun p =>
  if p.1 < tableLimit alphabet states then tableMemory machine p
  else encodedMemory (5 * (alphabet * states)) c p
end SmcTuring.Dolan.Table
namespace SmcTuring.Dolan.Mov
open Encoding Table
@[expose] def loadCandidateProgram : List Instruction := [.load .x .transition .zero, .load .x .x .zero, .load .y .current .zero]
@[expose] def loadSymbolProgram : List Instruction := [.load .y .transition .zero, .load .y .y .one, .load .y .y .zero]
@[expose] def loadDirectionProgram : List Instruction := [.load .direction .transition .zero, .load .direction .direction .one,
   .load .direction .direction .one, .load .direction .direction .zero]
/-- Read the next candidate and the destination-state list before selecting.
The choice is the symbol-comparison flag; no conditional branch is emitted. -/
@[expose] def loadCursorChoicesProgram : List Instruction := [.load .x .transition .one, .load .y .transition .zero,
   .load .y .y .one, .load .y .y .one, .load .y .y .one, .load .y .y .zero]
@[expose] def cursorSelectionProgram : List Instruction := [.store .scratch .zero .x, .store .scratch .one .y, .load .transition .scratch .matched]
@[expose] def updateCursorProgram : List Instruction := loadCursorChoicesProgram ++ cursorSelectionProgram
end SmcTuring.Dolan.Mov
namespace SmcTuring.Dolan.Mov
open Encoding Table
@[expose] def matchCandidateProgram : List Instruction := loadCandidateProgram ++ comparison
end SmcTuring.Dolan.Mov
namespace SmcTuring.Dolan.Mov
/-- Guard the sentinel before dereferencing a candidate. The comparison saves
and restores the cursor's first word. A zero result is dereferenced to halt;
a nonzero result selects the valid scratch cell. This is the corrected polarity. -/
@[expose] def guardProgram : List Instruction := [.load .x .transition .zero,
   .store .scratch .zero .one, .store .transition .zero .zero,
   .load .halted .scratch .zero, .store .transition .zero .x,
   .store .scratch .zero .zero, .store .scratch .one .scratch,
   .load .x .scratch .halted, .load .x .x .zero]
end SmcTuring.Dolan.Mov
namespace SmcTuring.Dolan.Mov
/-- The new symbol is supplied by Y after the linked-table loads. Unlike the
constant-symbol variant, this is one fixed five-instruction program. -/
@[expose] def writeValueProgram : List Instruction := [.load .x .current .zero] ++ selection ++ [.store .current .zero .value]
end SmcTuring.Dolan.Mov
namespace SmcTuring.Dolan.Mov
open Encoding Table
@[expose] def CoreRep (s : State) : Prop := s.registers .scratch = .address 0 ∧ s.registers .zero = .offset false ∧
    s.registers .one = .offset true
@[expose] def RuntimeRep {alphabet states : Nat} (machine : TM.Machine alphabet states) (c : TM.Configuration alphabet states) (s : State) : Prop := CoreRep s ∧ TapeRep (tapeLayout alphabet states) c s ∧ TableRep machine s.memory
end SmcTuring.Dolan.Mov
namespace SmcTuring.Dolan.Mov
open Encoding Table
/-- One fixed, machine-independent body. Machine information is read from
the linked transition table. Repetition supplies one unconditional backedge. -/
@[expose] def kernelProgram : List Instruction := guardProgram ++ (matchCandidateProgram ++ (loadSymbolProgram ++
    (writeValueProgram ++ (loadDirectionProgram ++ (advanceProgram ++ updateCursorProgram)))))
end SmcTuring.Dolan.Mov
namespace SmcTuring.Dolan.Mov
open Encoding Table
@[expose] def ScanRep {alphabet states : Nat} (machine : TM.Machine alphabet states) (c : TM.Configuration alphabet states) (index : Nat) (s : State) : Prop := RuntimeRep machine c s ∧ s.registers .transition = .address (cursor machine c.state index) ∧
    index ≤ (entries machine c.state).length ∧
    ∀ j : Fin (entries machine c.state).length, j.val < index →
      (entries machine c.state)[j.val].trigger ≠ c.tape c.head
@[expose] def initialKernelState {alphabet states : Nat} (machine : TM.Machine alphabet states) (c : TM.Configuration alphabet states) : State :=
  { registers := fun r => match r with
      | .scratch => .address 0
      | .zero => .offset false
      | .one => .offset true
      | .transition => .address (head machine c.state)
      | .current => .address ((tapeLayout alphabet states).cell c.head)
      | .left => .address ((tapeLayout alphabet states).cell (c.head - 1))
      | .right => .address ((tapeLayout alphabet states).cell (c.head + 1))
      | _ => .offset false
    memory := initialMemory machine c }
end SmcTuring.Dolan.Mov
namespace SmcTuring.Dolan.Four
open Mov
/-- The target machine has exactly these four physical registers. -/
inductive Register where
  | ring | a | b | c
  deriving DecidableEq, Repr
inductive Instruction where
  | immediate (dest : Register) (value : Word)
  | load (dest base offset : Register)
  | store (base offset source : Register)
  deriving DecidableEq, Repr
structure State where
  registers : Register → Word
  memory : Memory
@[expose] def address (s : State) (base offset : Register) : Option (Nat × Bool) := match s.registers base, s.registers offset with
  | .address cell, .offset choice => some (cell, choice)
  | _, _ => none
@[expose] def execute (i : Instruction) (s : State) : Option State := match i with
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
@[expose] def slot : Mov.Register → Fin 13
  | .zero => ⟨0, by decide⟩
  | .one => ⟨1, by decide⟩
  | .transition => ⟨2, by decide⟩
  | .current => ⟨3, by decide⟩
  | .left => ⟨4, by decide⟩
  | .right => ⟨5, by decide⟩
  | .scratch => ⟨6, by decide⟩
  | .x => ⟨7, by decide⟩
  | .y => ⟨8, by decide⟩
  | .matched => ⟨9, by decide⟩
  | .value => ⟨10, by decide⟩
  | .direction => ⟨11, by decide⟩
  | .halted => ⟨12, by decide⟩
@[expose] def registerAt (index : Fin 13) : Mov.Register := match index.val with
  | 0 => .zero
  | 1 => .one
  | 2 => .transition
  | 3 => .current
  | 4 => .left
  | 5 => .right
  | 6 => .scratch
  | 7 => .x
  | 8 => .y
  | 9 => .matched
  | 10 => .value
  | 11 => .direction
  | _ => .halted
/-- Reserve thirteen cells for the virtual registers. Both words of every
source heap cell are shifted above that prefix, including scratch and symbols. -/
@[expose] def encode : Word → Word
  | .address cell => .address (cell + 13)
  | .offset choice => .offset choice
@[expose] def initialMemory (source : Mov.State) : Memory := fun p =>
  if h : p.1 < 13 then
    if p.2 then .address ((p.1 + 1) % 13)
    else encode (source.registers (registerAt ⟨p.1, h⟩))
  else encode (source.memory (p.1 - 13, p.2))
@[expose] def initialState (source : Mov.State) : State :=
  { registers := fun r => if r = .ring then .address 0 else .offset false
    memory := initialMemory source }
end SmcTuring.Dolan.Four
namespace SmcTuring.SMC
open Dolan
structure Layout where
  base : Int
  stride : Int
  reserved : Nat
  base_nonnegative : 0 ≤ base
  stride_positive : 0 < stride
  enough_reserved : 4 ≤ reserved
@[expose] def fieldAddress (layout : Layout) (index : Nat) : Int := layout.base + layout.stride * (index : Int)
@[expose] def heapBase (layout : Layout) : Int := fieldAddress layout layout.reserved
@[expose] def heapField (layout : Layout) (p : Nat × Bool) : Int := fieldAddress layout (layout.reserved + 2 * p.1 + (if p.2 then 1 else 0))
@[expose] def encodeWord (layout : Layout) : Mov.Word → Int
  | .address cell => heapField layout (cell, false)
  | .offset choice => if choice then layout.stride else 0
end SmcTuring.SMC
namespace SmcTuring.SMC
/-- Execution fetches each header from the image and resolves its operands
from the current memory. It follows the executed instruction's actual PC. -/
@[expose] def runImage (wordBytes : Int) (image : Image) : Nat → State → Option State
  | 0, s => some s
  | count + 1, s => (step wordBytes image s).bind (runImage wordBytes image count)
@[expose] def PureSteps (wordBytes : Int) (image : Image) : Nat → State → Prop
  | 0, _ => True
  | count + 1, s =>
    match fetch image s with
    | none => False
    | some (instruction, next) => WritesCode image.codeField wordBytes instruction s ∧
        PureSteps wordBytes image count (execute wordBytes instruction next s)
namespace Lowering
open Dolan
end Lowering
@[expose] def ChangesCode (codeField : Int → Prop) (wordBytes : Int) (instruction : Instruction) (next : Int) (s : State) : Prop := ∃ field, codeField field ∧ (execute wordBytes instruction next s).memory field ≠ s.memory field
end SmcTuring.SMC
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
@[expose] def eval (initial : Int → Int) (address : Address) (s : State) : Int := match address with
  | .fixed value => value
  | .accumulator => s.acc
  | .operand field => lookup initial s.changes field
@[expose] def decode (initial : Int → Int) (header : Header) (s : State) : Instruction := match header with
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
/-- An executable list-update algorithm, independently defined from the
function-memory semantics. Each computational instruction appends one record. -/
@[expose] def execute (wordBytes : Int) (initial : Int → Int) (instruction : Instruction) (next : Int) (s : State) : State := match instruction with
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
@[expose] def step (wordBytes : Int) (headers : Int → Option (Header × Int)) (initial : Int → Int) (s : State) : Option State := (headers s.pc).map fun entry => execute wordBytes initial (decode initial entry.1 s) entry.2 s
@[expose] def run (wordBytes : Int) (headers : Int → Option (Header × Int)) (initial : Int → Int) : Nat → State → Option State
  | 0, s => some s
  | count + 1, s => (step wordBytes headers initial s).bind (run wordBytes headers initial count)
end SmcTuring.SMC.Finite
namespace SmcTuring.SMC.Effective
abbrev Journal := List (Nat × Nat)
@[expose] def journalCode (changes : List (Int × Int)) : Journal := changes.map fun entry => (Dolan.Encoding.zigzag entry.1, Dolan.Encoding.zigzag entry.2)
end SmcTuring.SMC.Effective
namespace SmcTuring.SMC.Effective
open Dolan.Encoding
/-- A finite, canonically encodable execution state. -/
abbrev StateCode := Nat × Nat × Nat × Bool × Journal
@[expose] def stateCode (s : Finite.State) : StateCode := (zigzag s.acc, zigzag s.stack, zigzag s.pc, s.carry, journalCode s.changes)
end SmcTuring.SMC.Effective
namespace SmcTuring.SMC.Virtual
open Dolan
/-- The checked 64-MOV logical kernel can be lowered directly. Its thirteen
registers become code words, so they are not thirteen hardware registers.
The separate checked four-register Dolan compiler remains available. -/
structure Layout where
  data : SMC.Layout
  enoughRegisters : 13 ≤ data.reserved
@[expose] def registerField (layout : Layout) (r : Mov.Register) : Int := fieldAddress layout.data (Four.slot r).val
@[expose] def Rep (layout : Layout) (source : Mov.State) (target : State) : Prop := (∀ r, target.memory (registerField layout r) = encodeWord layout.data (source.registers r)) ∧
  (∀ p, target.memory (heapField layout.data p) = encodeWord layout.data (source.memory p))
end SmcTuring.SMC.Virtual
namespace SmcTuring.SMC.Virtual
open Dolan
@[expose] def fieldIndex (layout : SMC.Layout) (address : Int) : Nat := ((address - layout.base) / layout.stride).toNat
/-- An arithmetic default generator for the data template pool. Metadata is
initialized separately by finitely many code-field writes. Instantiating the
source with the checked TM initializer queries only its finite table/input and
blank/link template; it does not use any future execution information. -/
@[expose] def dataMemory (layout : Layout) (source : Mov.State) : Int → Int := fun address =>
  let index := fieldIndex layout.data address
  if h : index < 13 then
    encodeWord layout.data (source.registers (Four.registerAt ⟨index, h⟩))
  else
    let cellWord := index - layout.data.reserved
    encodeWord layout.data (source.memory (cellWord / 2, decide (cellWord % 2 = 1)))
end SmcTuring.SMC.Virtual
namespace SmcTuring.SMC.Concrete
open Dolan
/-- Word addresses for the unbounded witness. Thirteen nonnegative fields are
logical registers; subsequent fields are the two-word source heap. Metadata
occupies exactly -1 through -38, separate from that data grid. -/
@[expose] def dataLayout : Virtual.Layout :=
  { data := { base := 0, stride := 1, reserved := 13,
              base_nonnegative := by decide, stride_positive := by decide, enough_reserved := by decide }
    enoughRegisters := by decide }
@[expose] def metaField (index : Nat) : Int := -((index : Int) + 1)
@[expose] def readerLabel (index : Nat) : Int := metaField index
@[expose] def readerPC (index : Nat) : Int := 8 * (index : Int)
@[expose] def captureLabel (sense : Bool) : Int := metaField (if sense then 24 else 23)
@[expose] def guardPC (sense : Bool) : Int := if sense then 224 else 184
@[expose] def kernelPC : Int := 264
@[expose] def terminalPC : Int := 1000000
@[expose] def topField : Int := metaField 25
@[expose] def returnField : Int := metaField 26
@[expose] def candidateField : Int := metaField 27
@[expose] def boundaryField : Int := metaField 28
@[expose] def zeroField : Int := metaField 29
@[expose] def resumeField : Int := metaField 30
@[expose] def terminalField : Int := metaField 31
@[expose] def maskField : Int := metaField 32
@[expose] def scratchField : Int := metaField 33
@[expose] def selectedField : Int := metaField 34
@[expose] def loopField : Int := metaField 35
@[expose] def offsetZeroField : Int := metaField 36
@[expose] def offsetOneField : Int := metaField 37
@[expose] def pointerLabel : Int := readerLabel 22
@[expose] def callProgram (target : Address) : List Header := stackResetProgram topField ++ [.call target]
@[expose] def readOp (reader : Nat) (operation : Header) : List Header := callProgram (.fixed (readerPC reader)) ++ [operation]
@[expose] def readerProgram (reader : Nat) : List Header := readProgram (readerLabel reader) ++ stackResetProgram topField ++ [.call (.operand returnField)]
/-- Two shared guards. `true` checks the offset tag (targets swapped), and
`false` checks the calculated base. Each saves the caller's return PC first. -/
@[expose] def guardProgram (sense : Bool) : List Header := let cont := if sense then 17 else 16
  let stop := if sense then 16 else 17
  readProgram (captureLabel sense) ++ [.store (.fixed resumeField)] ++
    readOp 13 (.store (.fixed scratchField)) ++ readOp 14 (.subtract scratchField) ++
    readOp 15 (.store (.fixed maskField)) ++ [.subtractBorrowZero maskField] ++
    readOp cont (.store (.fixed selectedField)) ++ readOp stop (.bitXor selectedField) ++
    readOp 18 (.bitAnd selectedField) ++ readOp cont (.bitXor selectedField) ++
    callProgram (.operand selectedField)
@[expose] def sourceRegister (r : Mov.Register) : Int := ((Four.slot r).val : Int)
@[expose] def addressProgram (base offset : Mov.Register) : List Header := readOp (Four.slot offset).val (.store (.fixed candidateField)) ++ callProgram (.fixed (guardPC true)) ++
    readOp (Four.slot base).val (.store (.fixed pointerLabel)) ++
    readOp (Four.slot offset).val (.add pointerLabel) ++
    readOp 21 (.store (.fixed candidateField)) ++ callProgram (.fixed (guardPC false))
/-- Address immediates are outside this fixed kernel's grammar. Their explicit
terminal block is never used by the proved supported-kernel check. -/
@[expose] def compileInstruction : Mov.Instruction → List Header
  | .immediate dest (.offset value) =>
      readOp (if value then 20 else 19) (.store (.fixed (sourceRegister dest)))
  | .immediate _ (.address _) => callProgram (.fixed terminalPC)
  | .load dest base offset =>
      addressProgram base offset ++ readOp 22 (.store (.fixed (sourceRegister dest)))
  | .store base offset source =>
      addressProgram base offset ++ callProgram (.fixed (readerPC (Four.slot source).val)) ++
        callProgram (.fixed (readerPC 22 + 3))
@[expose] def compileProgram (program : List Mov.Instruction) : List Header := program.flatMap compileInstruction
@[expose] def kernelProgram : List Header := compileProgram Mov.kernelProgram ++ callProgram (.operand loopField)
/-- The finite control graph is decoded by quotient/remainder and finite list
lookup. None of its headers depends on the input TM or its future execution. -/
@[expose] def controlHeader (pc : Nat) : Option Header := if pc < 184 then (readerProgram (pc / 8))[pc % 8]?
  else if pc < 224 then (guardProgram false)[pc - 184]?
  else if pc < 264 then (guardProgram true)[pc - 224]?
  else kernelProgram[pc - 264]?
/-- Storage-only template headers have negative PCs: even magnitudes own
nonnegative data fields; odd magnitudes own inactive metadata slots. -/
@[expose] def storageHeader (pc : Int) : Option Header := let magnitude := (-pc).toNat
  if magnitude % 2 = 0 then some (.store (.operand (((magnitude / 2 - 1 : Nat) : Int))))
  else
    let index := (magnitude - 1) / 2
    if 25 ≤ index ∧ index < 38 then some (.store (.operand (metaField index))) else none
@[expose] def headers (pc : Int) : Option (Header × Int) := (if 0 ≤ pc then controlHeader pc.toNat else storageHeader pc).map (fun header => (header, pc + 1))
@[expose] def owner (field : Int) : Int := if 0 ≤ field then -2 * (field + 1)
  else
    let index := (-field - 1).toNat
    if index < 23 then readerPC index + 3
    else if index < 25 then guardPC (decide (index = 24)) + 3
    else -(2 * (index : Int) + 1)
@[expose] def Code (field : Int) : Prop := -38 ≤ field
theorem data_owner (field : Int) (nonnegative : 0 ≤ field) : headers (owner field) = some (.store (.operand field), owner field + 1) := by sorry
theorem metadata_owner (index : Nat) (bounded : index < 38) : headers (owner (metaField index)) = some (.store (.operand (metaField index)), owner (metaField index) + 1) := by sorry
@[expose] def image : Image where
  headers := headers
  templatePC := owner
  codeField := Code
  storageTemplate := by
    intro field code
    refine ⟨owner field + 1, ?_⟩
    by_cases nonnegative : 0 ≤ field
    · exact data_owner field nonnegative
    · have indexBound : (-field - 1).toNat < 38 := by simp only [Code] at code; omega
      have original : metaField ((-field - 1).toNat) = field := by
        change -(((-field - 1).toNat : Int) + 1) = field
        omega
      simpa only [original] using metadata_owner ((-field - 1).toNat) indexBound
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Effective
abbrev TransitionData (alphabet states : Nat) := Option (Prod (Fin alphabet) (Prod Bool (Fin states)))
abbrev FrozenData (alphabet states : Nat) := Prod (Fin alphabet) (Prod (Fin states) (List (List (TransitionData alphabet states))))
@[expose] def frozenEquiv (alphabet states : Nat) : Equiv (TM.FrozenMachine alphabet states) (FrozenData alphabet states) where
  toFun machine := (machine.blank, machine.start, machine.table)
  invFun data := { blank := data.1, start := data.2.1, table := data.2.2 }
  left_inv machine := by cases machine; rfl
  right_inv data := by rcases data with ⟨blank, start, table⟩; rfl
instance frozenPrimcodable (alphabet states : Nat) : Primcodable (TM.FrozenMachine alphabet states) := Primcodable.ofEquiv (FrozenData alphabet states) (frozenEquiv alphabet states)
variable {alphabet states : Nat}
end SmcTuring.SMC.Effective
namespace SmcTuring.SMC.Concrete
open Dolan
/-- Literal metadata, independently defined from the instruction semantics.
Slots 0..12 are reader pointers to register fields. Further readers point to
the named control words; the pointer reader has an initial scratch-cell target. -/
@[expose] def metadataValue (index : Nat) : Int := if index < 13 then (index : Int) else
    match index with
    | 13 => candidateField
    | 14 => boundaryField
    | 15 => zeroField
    | 16 => resumeField
    | 17 => terminalField
    | 18 => maskField
    | 19 => offsetZeroField
    | 20 => offsetOneField
    | 21 => pointerLabel
    | 22 => heapBase dataLayout.data
    | 23 | 24 => returnField
    | 25 => returnField + 1
    | 28 => heapBase dataLayout.data
    | 31 => terminalPC
    | 35 => kernelPC
    | 37 => 1
    | _ => 0
@[expose] def StaticSlot (index : Nat) : Prop := index < 38 ∧ index ≠ 22 ∧ index ≠ 26 ∧ index ≠ 27 ∧ index ≠ 30 ∧
    index ≠ 32 ∧ index ≠ 33 ∧ index ≠ 34
@[expose] def Static (s : State) : Prop := ∀ index, StaticSlot index → s.memory (metaField index) = metadataValue index
@[expose] def initialMemory (source : Mov.State) (field : Int) : Int := if 0 ≤ field then Virtual.dataMemory dataLayout source field
  else metadataValue (-field - 1).toNat
@[expose] def initialState (source : Mov.State) : State :=
  { acc := 0, stack := returnField, pc := kernelPC, carry := false, memory := initialMemory source }
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
open Dolan
@[expose] def Executes (count : Nat) (start finish : State) : Prop := runImage 1 image count start = some finish ∧ PureSteps 1 image count start
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
open Dolan
@[expose] def instructionCount : Mov.Instruction → Nat
  | .immediate _ (.offset _) => 11
  | .immediate _ (.address _) => 3
  | .load _ _ _ => 233
  | .store _ _ _ => 239
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
open Dolan
@[expose] def programCount : List Mov.Instruction → Nat
  | [] => 0
  | instruction :: rest => instructionCount instruction + programCount rest
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
open Dolan
@[expose] def kernelCount : Nat := programCount Mov.kernelProgram + 3
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
open Dolan
/-- The unbounded SMC image is fixed. Its initial words are computed from a
finite transition table and finite input through the checked Dolan initializer. -/
@[expose] def initialTMState {alphabet states : Nat} (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) : State := initialState (Mov.initialKernelState machine (TM.initialConfiguration machine input))
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
open Dolan
@[expose] def ReachesTerminal (s : State) : Prop := ∃ count finish, runImage 1 image count s = some finish ∧ finish.pc = terminalPC
@[expose] def RunsForever (s : State) : Prop := ∀ count, ∃ finish, runImage 1 image count s = some finish
@[expose] def PureComputation (s : State) : Prop := ∀ count finish, runImage 1 image count s = some finish → PureSteps 1 image count s
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
open Dolan
structure TMTraceSpec {alphabet states : Nat} (machine : TM.Machine alphabet states) (configuration : TM.Configuration alphabet states) (source : Mov.State) (start finish : State) (steps passes : Nat) : Prop where
  progress : steps ≤ passes
  executed : Executes (passes * kernelCount) start finish
  static : Static finish
  pc : finish.pc = kernelPC
  scanned : Mov.ScanRep machine configuration 0 source
  represented : Virtual.Rep dataLayout source finish
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
open Dolan
@[expose] def CodeChangeAt (start : State) (time : Nat) : Prop := ∃ s instruction next, runImage 1 image time start = some s ∧ fetch image s = some (instruction, next) ∧
    ChangesCode image.codeField 1 instruction next s
@[expose] def InfinitelyChanges (s : State) : Prop := ∀ bound, ∃ time, bound ≤ time ∧ CodeChangeAt s time
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
open Dolan
@[expose] def FieldChangeAt (start : State) (time : Nat) (field : Int) : Prop := ∃ s instruction next, runImage 1 image time start = some s ∧
    fetch image s = some (instruction, next) ∧
    (execute 1 instruction next s).memory field ≠ s.memory field
/-- Actual fetched changes occur in fields beyond every finite address bound.
This is stronger than infinitely many changes in a fixed finite set of fields. -/
@[expose] def UnboundedChangedFields (start : State) : Prop := ∀ bound : Nat, ∃ field time, (bound : Int) < field ∧ image.codeField field ∧ FieldChangeAt start time field
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
open Dolan
/-- Recover the complete two-sided output tape and the head from code words. -/
@[expose] def TapeWords {alphabet states : Nat} (configuration : TM.Configuration alphabet states) (s : State) : Prop := s.memory (Virtual.registerField dataLayout .current) =
      encodeWord dataLayout.data (.address ((Table.tapeLayout alphabet states).cell configuration.head)) ∧
    ∀ position, s.memory (heapField dataLayout.data ((Table.tapeLayout alphabet states).cell position, false)) =
      encodeWord dataLayout.data (.address ((Table.tapeLayout alphabet states).symbol (configuration.tape position)))
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Concrete
/-- This finite register/journal record contains no memory or header function. -/
@[expose] def initialDescription : Finite.State :=
  { acc := 0, stack := returnField, pc := kernelPC, carry := false, changes := [] }
/-- A closed default-word algorithm whose only external inputs are a finite
transition table, finite input list and queried integer address. -/
@[expose] def initialWords {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (field : Int) : Int := (initialTMState (TM.thaw machine) input).memory field
/-- A terminating bounded evaluator over finite data. Header lookup and initial
word lookup are the fixed arithmetic/list algorithms, not caller-supplied oracles. -/
@[expose] def finiteRun {alphabet states : Nat} (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (count : Nat) : Option Finite.State := Finite.run 1 headers (initialWords machine input) count initialDescription
end SmcTuring.SMC.Concrete
namespace SmcTuring.SMC.Effective
open Dolan.Encoding
variable {alphabet states : Nat}
abbrev SearchInput (alphabet states : Nat) := Prod (TM.FrozenMachine alphabet states) (List (Fin alphabet))
/-- A finite prefix is a successful search result only at the actual terminal
PC. Missing headers and nonterminal states are rejected. -/
@[expose] def terminalPrefix (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (count : Nat) : Option StateCode := ((Concrete.finiteRun machine input count).map stateCode).bind fun state =>
    if state.2.2.1 = zigzag Concrete.terminalPC then some state else none
/-- Search increasing finite prefixes. The result is the complete coded journal
state; divergence has no result. Both machine and input are finite data. -/
@[expose] def terminalSearch (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) : Part StateCode := Nat.rfindOpt (terminalPrefix machine input)
end SmcTuring.SMC.Effective
namespace SmcTuring.SMC.Effective
open Turing
variable {alphabet states : Nat}
abbrev InterpreterAlphabet := TM2to1.Γ' PartrecToTM2.K' (fun _ => PartrecToTM2.Γ')
end SmcTuring.SMC.Effective
namespace SmcTuring.MathlibTM0
variable {alphabet states : Nat} [Inhabited (Fin alphabet)] [Inhabited (Fin states)]
@[expose] def original (state : Fin states) : Fin (2 * states) := ⟨state.val, by have := state.isLt; omega⟩
@[expose] def restoring (state : Fin states) : Fin (2 * states) := ⟨states + state.val, by have := state.isLt; omega⟩
@[expose] def direction : Turing.Dir → Bool
  | .left => false
  | .right => true
@[expose] def entry (symbol : Fin alphabet) (next : Fin states) : Turing.TM0.Stmt (Fin alphabet) → Fin alphabet × Bool × Fin (2 * states)
  | .move dir => (symbol, direction dir, original next)
  | .write value => (value, true, restoring next)
/-- Compile the actual Mathlib TM0 machine to the finite write/move model.
A write moves right temporarily; the restoring phase rewrites the neighbor
with its current value and moves left. There are exactly twice as many labels. -/
@[expose] def compile (machine : Turing.TM0.Machine (Fin alphabet) (Fin states)) : TM.Machine alphabet (2 * states) :=
  { blank := default
    start := original default
    transition := fun state symbol =>
      if h : state.val < states then
        (machine ⟨state.val, h⟩ symbol).map fun result => entry symbol result.1 result.2
      else some (symbol, false, original ⟨state.val - states, by have := state.isLt; omega⟩) }
/-- Mathlib's tape is head-relative. The source's absolute coordinate is carried
by this relation, and every relative position is observed, on both sides. -/
@[expose] def Rep (library : Turing.TM0.Cfg (Fin alphabet) (Fin states)) (source : TM.Configuration alphabet (2 * states)) : Prop := source.state = original library.q ∧ ∀ position : Int, source.tape (source.head + position) = library.Tape.nth position
end SmcTuring.MathlibTM0
namespace SmcTuring.MathlibTM0.Numbering
open Turing
variable {Symbol Label NewSymbol NewLabel : Type}
  [Inhabited Symbol] [Inhabited Label] [Inhabited NewSymbol] [Inhabited NewLabel]
/-- Encode the alphabet while explicitly preserving its blank. -/
@[expose] def symbolMap (symbols : Symbol ≃ NewSymbol) (blank : symbols default = default) : PointedMap Symbol NewSymbol := ⟨symbols, blank⟩
variable (machine : TM0.Machine Symbol Label)
  (symbols : Symbol ≃ NewSymbol) (blank : symbols default = default)
  (labels : Label ≃ NewLabel) (initial : labels default = default)
end SmcTuring.MathlibTM0.Numbering
namespace SmcTuring.SMC.Effective
open Turing
variable {alphabet states alphabetCount labelCount : Nat}
/-- The interpreter receives only the finite encoded table/input descriptor. -/
@[expose] def searchTape (input : SearchInput alphabet states) : List InterpreterAlphabet := TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [Encodable.encode input])
/-- The numbered output carries the complete returned journal on its main track. -/
@[expose] def JournalOutput [Inhabited (Fin alphabetCount)] (symbols : InterpreterAlphabet ≃ Fin alphabetCount) (blank : symbols default = default) (journal : StateCode) (output : ListBlank (Fin alphabetCount)) : Prop := ∃ tracks : ListBlank (PartrecToTM2.K' -> Option PartrecToTM2.Γ'),
    (TM2to1.addBottom tracks).map (MathlibTM0.Numbering.symbolMap symbols blank) = output ∧
    tracks.map (PointedMap.mk (fun row : PartrecToTM2.K' -> Option PartrecToTM2.Γ' => row .main) rfl) =
      ListBlank.mk ((PartrecToTM2.trList [Encodable.encode journal]).map some).reverse
/-- The fixed pure SMC compiler starts from the numbered finite input. -/
@[expose] def numberedInitial [Inhabited (Fin alphabetCount)] [Inhabited (Fin labelCount)] (numbered : TM0.Machine (Fin alphabetCount) (Fin labelCount)) (symbols : InterpreterAlphabet ≃ Fin alphabetCount) (input : SearchInput alphabet states) : State := Concrete.initialTMState (MathlibTM0.compile numbered) ((searchTape input).map symbols)
end SmcTuring.SMC.Effective
namespace SmcTuring.Dolan.Four
@[expose] def repeatRun (program : List Instruction) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (run program s).bind (repeatRun program n)
@[expose] def LoopHalts (program : List Instruction) (s : State) : Prop := ∃ n finish, repeatRun program n s = some finish ∧ run program finish = none
@[expose] def LoopDiverges (program : List Instruction) (s : State) : Prop := ∀ n, ∃ finish, repeatRun program n s = some finish
end SmcTuring.Dolan.Four
namespace SmcTuring.CorrectedPaper
open SMC SMC.Effective Turing
/-- Unbounded integer-address semantics for the paper's mathematical claim.
The fixed pure image simulates every finite source TM,including divergence
and infinitely many actual fetched code changes. -/
@[expose] def Unbounded : Prop := (∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet)),
    (Concrete.ReachesTerminal (Concrete.initialTMState machine input) ↔ TM.Halts machine (TM.initialConfiguration machine input)) ∧
    (Concrete.RunsForever (Concrete.initialTMState machine input) ↔ TM.Diverges machine (TM.initialConfiguration machine input)) ∧
    Concrete.PureComputation (Concrete.initialTMState machine input) ∧
    (TM.Diverges machine (TM.initialConfiguration machine input) → Concrete.InfinitelyChanges (Concrete.initialTMState machine input))) ∧
  ∃ start : SMC.State,Concrete.RunsForever start ∧ Concrete.PureComputation start ∧
    Concrete.InfinitelyChanges start ∧ Concrete.UnboundedChangedFields start
/-- Dolan foundation:four registers,three MOV forms,static body and an
unconditional backedge,in the disclosed unbounded invalid-zero model. -/
@[expose] def FourMov : Prop := ∃ program : List Dolan.Four.Instruction,
    ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet)),
      let configuration := TM.initialConfiguration machine input
      let initial := Dolan.Four.initialState (Dolan.Mov.initialKernelState machine configuration)
      (Dolan.Four.LoopHalts program initial ↔ TM.Halts machine configuration) ∧
      (Dolan.Four.LoopDiverges program initial ↔ TM.Diverges machine configuration)
/-- An effective finite-alphabet interpreter receives the encoded finite
machine/input only. It preserves halt/divergence,purity and terminal journals. -/
@[expose] def EffectiveInterpreter : Prop := ∀ (alphabet states : Nat),
    ∃ (alphabetCount labelCount : Nat) (symbols : InterpreterAlphabet ≃ Fin alphabetCount)
      (start : Fin labelCount),
      letI : Inhabited (Fin alphabetCount) := ⟨symbols default⟩
      letI : Inhabited (Fin labelCount) := ⟨start⟩
      ∃ numbered : TM0.Machine (Fin alphabetCount) (Fin labelCount),
        ∀ input : SearchInput alphabet states,
          (Concrete.ReachesTerminal (numberedInitial numbered symbols input) ↔
            TM.Halts (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2)) ∧
          (Concrete.RunsForever (numberedInitial numbered symbols input) ↔
            TM.Diverges (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2)) ∧
          Concrete.PureComputation (numberedInitial numbered symbols input) ∧
          (TM.Diverges (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2) ->
            Concrete.InfinitelyChanges (numberedInitial numbered symbols input)) ∧
          ∀ (count : Nat) (finish : State),
            runImage 1 Concrete.image count (numberedInitial numbered symbols input) = some finish ->
            finish.pc = Concrete.terminalPC ->
            ∃ (journal : StateCode) (library : TM0.Cfg (Fin alphabetCount) (Fin labelCount))
              (source : TM.Configuration alphabetCount (2 * labelCount)),
              journal ∈ terminalSearch input.1 input.2 ∧
              JournalOutput symbols rfl journal library.Tape.right₀ ∧
              MathlibTM0.Rep library source ∧ Concrete.TapeWords source finish
/-- Every finite source configuration is observed on the SAME pure trace:
full tape at all integer positions and the logical head link. -/
@[expose] def Observations : Prop := ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet))
    (steps : Nat) (configuration : TM.Configuration alphabet states),
    TM.run machine steps (TM.initialConfiguration machine input)=some configuration →
    ∃ (passes : Nat) (source : Dolan.Mov.State) (finish : SMC.State),
      Concrete.TMTraceSpec machine configuration source (Concrete.initialTMState machine input) finish steps passes ∧
      finish.memory (Virtual.registerField Concrete.dataLayout .current)=
        encodeWord Concrete.dataLayout.data (.address ((Dolan.Table.tapeLayout alphabet states).cell configuration.head)) ∧
      ∀ position : Int,finish.memory (heapField Concrete.dataLayout.data ((Dolan.Table.tapeLayout alphabet states).cell position,false))=
        encodeWord Concrete.dataLayout.data (.address ((Dolan.Table.tapeLayout alphabet states).symbol (configuration.tape position)))
end SmcTuring.CorrectedPaper
namespace PalomarSMC
/-- Halt/divergence,purity,unbounded fresh fetched changes,finite effective
interpreter terminal journals,and every source-prefix full tape/logical head. -/
theorem mathematical_result : SmcTuring.CorrectedPaper.Unbounded ∧ SmcTuring.CorrectedPaper.FourMov ∧ SmcTuring.CorrectedPaper.EffectiveInterpreter ∧ SmcTuring.CorrectedPaper.Observations := by
  sorry
end PalomarSMC

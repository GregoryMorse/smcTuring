module
public import SmcTuring.Dolan.Simulation

public section

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

@[expose] def address (s : State) (base offset : Register) : Option (Nat × Bool) :=
  match s.registers base, s.registers offset with
  | .address cell, .offset choice => some (cell, choice)
  | _, _ => none

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

@[expose] def registerAt (index : Fin 13) : Mov.Register :=
  match index.val with
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

theorem register_at_slot (r : Mov.Register) : registerAt (slot r) = r := by cases r <;> rfl

theorem slot_injective : Function.Injective slot := by
  intro a b equal
  have same := congrArg registerAt equal
  simpa [register_at_slot] using same

/-- Reserve thirteen cells for the virtual registers. Both words of every
source heap cell are shifted above that prefix, including scratch and symbols. -/
@[expose] def encode : Word → Word
  | .address cell => .address (cell + 13)
  | .offset choice => .offset choice

theorem encode_injective : Function.Injective encode := by
  intro a b equal
  cases a <;> cases b <;> simp_all [encode]

@[expose] def Coherent (source : Mov.State) (target : State) (ringIndex : Fin 13) : Prop :=
  target.registers .ring = .address ringIndex.val ∧
  (∀ r, target.memory ((slot r).val, false) = encode (source.registers r)) ∧
  (∀ i : Fin 13, target.memory (i.val, true) = .address ((i.val + 1) % 13)) ∧
  (∀ p, target.memory (p.1 + 13, p.2) = encode (source.memory p))

@[expose] def initialMemory (source : Mov.State) : Memory := fun p =>
  if h : p.1 < 13 then
    if p.2 then .address ((p.1 + 1) % 13)
    else encode (source.registers (registerAt ⟨p.1, h⟩))
  else encode (source.memory (p.1 - 13, p.2))

@[expose] def initialState (source : Mov.State) : State :=
  { registers := fun r => if r = .ring then .address 0 else .offset false
    memory := initialMemory source }

theorem initial_coherent (source : Mov.State) : Coherent source (initialState source) ⟨0, by decide⟩ := by
  refine ⟨by simp [initialState], ?_, ?_, ?_⟩
  · intro r
    simp [initialState, initialMemory, (slot r).isLt, register_at_slot]
  · intro i
    simp [initialState, initialMemory, i.isLt]
  · intro p
    have high : ¬ p.1 + 13 < 13 := by omega
    simp [initialState, initialMemory, high]

/-- Updating a virtual register's first word preserves all ring links and all
source heap words, even when the source register itself contains a pointer. -/
theorem spill_coherent (source : Mov.State) (target : State) (ringIndex : Fin 13)
    (r : Mov.Register) (value : Word) (rep : Coherent source target ringIndex) :
    Coherent { source with registers := write source.registers r value }
      { target with memory := write target.memory ((slot r).val, false) (encode value) } ringIndex := by
  refine ⟨rep.1, ?_, ?_, ?_⟩
  · intro q
    by_cases equal : q = r
    · subst q
      simp [write]
    · have separate : (slot q).val ≠ (slot r).val := by
        intro same
        exact equal (slot_injective (Fin.ext same))
      simpa [write, equal, separate] using rep.2.1 q
  · intro i
    simpa [write] using rep.2.2.1 i
  · intro p
    have separate : p.1 + 13 ≠ (slot r).val := by have := (slot r).isLt; omega
    simpa [write, separate] using rep.2.2.2 p

/-- A source heap store cannot touch the virtual-register ring. -/
theorem heap_store_coherent (source : Mov.State) (target : State) (ringIndex : Fin 13)
    (p : Nat × Bool) (value : Word) (rep : Coherent source target ringIndex) :
    Coherent { source with memory := write source.memory p value }
      { target with memory := write target.memory (p.1 + 13, p.2) (encode value) } ringIndex := by
  refine ⟨rep.1, ?_, ?_, ?_⟩
  · intro r
    have separate : (slot r).val ≠ p.1 + 13 := by have := (slot r).isLt; omega
    simpa [write, separate] using rep.2.1 r
  · intro i
    have separate : i.val ≠ p.1 + 13 := by have := i.isLt; omega
    simpa [write, separate] using rep.2.2.1 i
  · intro q
    by_cases same : q = p
    · subst q
      simp [write]
    · have separate : (q.1 + 13, q.2) ≠ (p.1 + 13, p.2) := by
        intro equal
        apply same
        apply Prod.ext
        · have := congrArg Prod.fst equal
          omega
        · have second := congrArg (fun x : Nat × Bool => x.2) equal
          exact second
      simpa [write, same, separate] using rep.2.2.2 q

@[expose] def distance (origin destination : Fin 13) : Nat :=
  if origin.val ≤ destination.val then destination.val - origin.val else 13 - origin.val + destination.val

theorem distance_correct (origin destination : Fin 13) :
    (origin.val + distance origin destination) % 13 = destination.val := by
  have hf := origin.isLt
  have ht := destination.isLt
  by_cases h : origin.val ≤ destination.val
  · have equal : origin.val + (destination.val - origin.val) = destination.val := by omega
    simp [distance, h, equal, Nat.mod_eq_of_lt ht]
  · have equal : origin.val + (13 - origin.val + destination.val) = destination.val + 13 := by omega
    simp [distance, h, equal, Nat.mod_eq_of_lt ht]

/-- The ring is walked with MOV loads and a temporary holding offset one.
Each block's static source-register operands determine the walking distance. -/
@[expose] def walk (temporary : Register) (origin destination : Fin 13) : List Instruction :=
  [.immediate temporary (.offset true)] ++
    List.replicate (distance origin destination) (.load .ring .ring temporary)

@[expose] def fetch (temporary : Register) (origin : Fin 13) (r : Mov.Register) : List Instruction :=
  walk temporary origin (slot r) ++
    [.immediate temporary (.offset false), .load temporary .ring temporary]

@[expose] def spill (temporary value : Register) (origin : Fin 13) (r : Mov.Register) : List Instruction :=
  walk temporary origin (slot r) ++ [.immediate temporary (.offset false), .store .ring temporary value]

@[expose] def reset (temporary : Register) (origin : Fin 13) : List Instruction :=
  walk temporary origin ⟨0, by decide⟩

/-- Compile each of the three MOV forms. Every block starts and ends with the
ring cursor at zero; operands are fetched before a destination is overwritten. -/
@[expose] def compileInstruction : Mov.Instruction → List Instruction
  | .immediate dest value =>
    [.immediate .a (encode value)] ++ spill .b .a ⟨0, by decide⟩ dest ++ reset .b (slot dest)
  | .load dest base offset =>
    fetch .a ⟨0, by decide⟩ base ++ fetch .b (slot base) offset ++
    [.load .a .a .b] ++ spill .b .a (slot offset) dest ++ reset .b (slot dest)
  | .store base offset source =>
    fetch .a ⟨0, by decide⟩ base ++ fetch .b (slot base) offset ++ fetch .c (slot offset) source ++
    [.store .a .b .c] ++ reset .a (slot source)

@[expose] def compile (program : List Mov.Instruction) : List Instruction :=
  program.flatMap compileInstruction

end SmcTuring.Dolan.Four

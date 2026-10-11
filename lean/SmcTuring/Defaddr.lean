module
public import SmcTuring.Memory

public section

namespace SmcTuring.Defaddr

/-- The accumulator and unified word memory at a DEFADDR instruction boundary.
The word type can be Nat (unbounded) or BitVec 32/64 (fixed-width). -/
structure State (Word : Type) where
  acc : Word
  mem : Word → Word

/-- An operand address can be fixed, in the accumulator, or stored in code. -/
inductive Address (Word : Type) where
  | fixed (a : Word)
  | accumulator
  | field (a : Word)

@[expose] def Address.eval {Word : Type} (a : Address Word) (s : State Word) : Word :=
  match a with
  | .fixed p => p
  | .accumulator => s.acc
  | .field p => s.mem p

/-- Only the three instruction effects required by the original and repair. -/
inductive Instruction (Word : Type) where
  | exchange (a : Address Word)
  | store (a : Address Word)
  | load (a : Address Word)

@[expose] def execute {Word : Type} [DecidableEq Word]
    (i : Instruction Word) (s : State Word) : State Word :=
  let p := match i with
    | .exchange a | .store a | .load a => a.eval s
  match i with
  | .exchange _ => { acc := s.mem p, mem := write s.mem p s.acc }
  | .store _ => { s with mem := write s.mem p s.acc }
  | .load _ => { s with acc := s.mem p }

/-- Architectural memory writes, even if the value is unchanged. -/
@[expose] def footprint {Word : Type} (i : Instruction Word) (s : State Word) : List Word :=
  match i with
  | .exchange a | .store a => [a.eval s]
  | .load _ => []

@[expose] def run {Word : Type} [DecidableEq Word]
    (program : List (Instruction Word)) (s : State Word) : State Word :=
  program.foldl (fun state instruction => execute instruction state) s

/-- Listing 2's literal effects; label is the MOFFS operand field. -/
@[expose] def original {Word : Type} (label : Word) : List (Instruction Word) :=
  [.exchange (.fixed label), .store (.fixed label),
   .load .accumulator, .store (.field label)]

/-- Replace only the register-only indirect load by an indirect exchange. -/
@[expose] def corrected {Word : Type} (label : Word) : List (Instruction Word) :=
  [.exchange (.fixed label), .store (.fixed label),
   .exchange .accumulator, .store (.field label)]

/-- The two initial instructions read the pointer without changing memory. -/
theorem prefix_restores {Word : Type} [DecidableEq Word]
    (label : Word) (s : State Word) :
    run [.exchange (.fixed label), .store (.fixed label)] s =
      { acc := s.mem label, mem := s.mem } := by
  simp [run, execute, Address.eval]

/-- The original's boundary effect is a memory-preserving indirect load. -/
theorem original_effect {Word : Type} [DecidableEq Word]
    (label : Word) (s : State Word) :
    run (original label) s = { acc := s.mem (s.mem label), mem := s.mem } := by
  simp [original, run, execute, Address.eval]

/-- The repair has the same effect, including when the pointer equals label. -/
theorem corrected_effect {Word : Type} [DecidableEq Word]
    (label : Word) (s : State Word) :
    run (corrected label) s = { acc := s.mem (s.mem label), mem := s.mem } := by
  by_cases h : s.mem label = label
  · have hw : write s.mem label label = s.mem := by
      simpa [h] using (write_back s.mem label)
    simp [corrected, run, execute, Address.eval, h, hw]
  · have h' : label ≠ s.mem label := Ne.symm h
    simp [corrected, run, execute, Address.eval, h']

theorem repair_equivalent {Word : Type} [DecidableEq Word]
    (label : Word) (s : State Word) : run (corrected label) s = run (original label) s := by
  rw [corrected_effect, original_effect]

/-- Actual writes to code at each instruction, independent of value changes. -/
@[expose] def PureRun {Word : Type} [DecidableEq Word]
    (codeField : Word → Prop) : List (Instruction Word) → State Word → Prop
  | [], _ => True
  | i :: rest, s => footprint i s ≠ [] ∧
      (∀ p ∈ footprint i s, codeField p) ∧ PureRun codeField rest (execute i s)

/-- The literal sequence fails strict purity for every memory and accumulator. -/
theorem original_not_pure {Word : Type} [DecidableEq Word]
    (codeField : Word → Prop) (label : Word) (s : State Word) :
    ¬ PureRun codeField (original label) s := by
  simp [PureRun, original, footprint]

/-- Both the pointer field and pointed-to cell must really be code fields. -/
theorem corrected_pure {Word : Type} [DecidableEq Word]
    (codeField : Word → Prop) (label : Word) (s : State Word)
    (hl : codeField label) (hp : codeField (s.mem label)) :
    PureRun codeField (corrected label) s := by
  by_cases h : s.mem label = label
  · simp [PureRun, corrected, footprint, execute, Address.eval, write, h, hl]
  · have h' : label ≠ s.mem label := Ne.symm h
    simp [PureRun, corrected, footprint, execute, Address.eval, h', hl, hp]

/-- Fixed-width instances inherit the generic proof, without exhaustively testing words. -/
theorem repair32 (label : BitVec 32) (s : State (BitVec 32)) :
    run (corrected label) s = run (original label) s := repair_equivalent label s

theorem repair64 (label : BitVec 64) (s : State (BitVec 64)) :
    run (corrected label) s = run (original label) s := repair_equivalent label s

/-- Exact boundary result: the accumulator is not in general preserved. -/
theorem accumulator_result {Word : Type} [DecidableEq Word]
    (label : Word) (s : State Word) :
    (run (corrected label) s).acc = s.mem (s.mem label) := by
  rw [corrected_effect]

theorem run_append {Word : Type} [DecidableEq Word]
    (first second : List (Instruction Word)) (s : State Word) :
    run (first ++ second) s = run second (run first s) := by
  simp [run, List.foldl_append]

theorem pure_append {Word : Type} [DecidableEq Word]
    (codeField : Word → Prop) (first second : List (Instruction Word)) (s : State Word) :
    PureRun codeField (first ++ second) s ↔
      PureRun codeField first s ∧ PureRun codeField second (run first s) := by
  induction first generalizing s with
  | nil => simp [PureRun, run]
  | cons i rest ih =>
    simp [PureRun, run, ih, and_assoc]

/-- A trace consisting of any finite number of macro repetitions. This is not
a claim about a native loop instruction or about universal computation. -/
@[expose] def repetitions {Word : Type} (label : Word) : Nat → List (Instruction Word)
  | 0 => []
  | n + 1 => corrected label ++ repetitions label n

theorem arbitrary_repetitions_pure {Word : Type} [DecidableEq Word]
    (codeField : Word → Prop) (label : Word) (n : Nat) (s : State Word)
    (hl : codeField label) (hp : codeField (s.mem label)) :
    PureRun codeField (repetitions label n) s := by
  induction n generalizing s with
  | zero => simp [repetitions, PureRun]
  | succ n ih =>
    rw [repetitions, pure_append]
    constructor
    · exact corrected_pure codeField label s hl hp
    · rw [corrected_effect]
      exact ih { acc := s.mem (s.mem label), mem := s.mem } hp

theorem arbitrary_repetitions_restore_memory {Word : Type} [DecidableEq Word]
    (label : Word) (n : Nat) (s : State Word) :
    (run (repetitions label n) s).mem = s.mem := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [repetitions, run_append, corrected_effect]
    exact ih { acc := s.mem (s.mem label), mem := s.mem }

end SmcTuring.Defaddr

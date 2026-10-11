module
public import SmcTuring.Dolan.TapeEncoding

public section

namespace SmcTuring.Dolan.Encoding

open Mov

/-- A computable bijective enumeration of the two-sided tape positions. -/
@[expose] def zigzag : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

@[expose] def unzigzag (n : Nat) : Int :=
  if n % 2 = 0 then .ofNat (n / 2) else .negSucc (n / 2)

theorem zigzag_injective : Function.Injective zigzag := by
  intro a b h
  cases a <;> cases b <;> simp_all [zigzag] <;> omega

@[simp] theorem unzigzag_zigzag (position : Int) : unzigzag (zigzag position) = position := by
  cases position <;> simp [zigzag, unzigzag] <;> omega

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

theorem symbol_injective (alphabet reserved : Nat) :
    Function.Injective (standardLayout alphabet reserved).symbol := by
  intro a b h
  apply Fin.ext
  simp only [standardLayout] at h
  omega

theorem symbol_tape_disjoint (alphabet reserved : Nat) (symbol : Fin alphabet)
    (position : Int) :
    (standardLayout alphabet reserved).symbol symbol ≠
      (standardLayout alphabet reserved).cell position := by
  have bound := symbol.isLt
  simp only [standardLayout]
  omega

/-- This is an explicit computable memory function, not an existentially
chosen oracle containing a future computation. The tape is blank except for
the supplied finite input when c is a standard initial configuration. -/
@[expose] def encodedMemory {alphabet states : Nat} (reserved : Nat)
    (c : TM.Configuration alphabet states) : Memory := fun p =>
  let base := alphabet + reserved + 1
  if p.1 < base then .offset false
  else
    let position := unzigzag (p.1 - base)
    if p.2 then
      .address ((standardLayout alphabet reserved).cell
        (if position < c.head then position - 1 else position + 1))
    else .address ((standardLayout alphabet reserved).symbol (c.tape position))

theorem encoded_memory_correct {alphabet states : Nat} (reserved : Nat)
    (c : TM.Configuration alphabet states) :
    MemoryRep (standardLayout alphabet reserved) c (encodedMemory reserved c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro position
    have notLow : ¬ alphabet + reserved + 1 + zigzag position < alphabet + reserved + 1 := by omega
    simp [encodedMemory, standardLayout, notLow]
  · intro position hp
    have notLow : ¬ alphabet + reserved + 1 + zigzag position < alphabet + reserved + 1 := by omega
    simp [encodedMemory, standardLayout, notLow, hp]
  · intro position hp
    have notLow : ¬ alphabet + reserved + 1 + zigzag position < alphabet + reserved + 1 := by omega
    have notLeft : ¬ position < c.head := by omega
    simp [encodedMemory, standardLayout, notLow, notLeft]

/-- The logical two-sided tape needs no runtime allocation oracle: its initial
memory is given by a computable blank/link template and finite input. -/
@[expose] def initialTapeState {alphabet states : Nat} (reserved : Nat)
    (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) : State :=
  let c := TM.initialConfiguration machine input
  let layout := standardLayout alphabet reserved
  { registers := fun r => match r with
      | .current => .address (layout.cell c.head)
      | .left => .address (layout.cell (c.head - 1))
      | .right => .address (layout.cell (c.head + 1))
      | .scratch => .address layout.scratch
      | .one => .offset true
      | _ => .offset false
    memory := encodedMemory reserved c }

theorem initial_tape_correct {alphabet states : Nat} (reserved : Nat)
    (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) :
    TapeRep (standardLayout alphabet reserved) (TM.initialConfiguration machine input)
      (initialTapeState reserved machine input) := by
  exact ⟨⟨rfl, rfl, rfl⟩, encoded_memory_correct reserved _⟩

end SmcTuring.Dolan.Encoding

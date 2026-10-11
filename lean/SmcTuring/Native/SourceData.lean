module
public import SmcTuring.Native.SourceValues
public import SmcTuring.Dolan.FourRegisters

public section

namespace SmcTuring.Native.SourceData

open Execution

@[expose] def Capacity (mode : Mode) (base cells : Nat) : Prop :=
  base + mode.stride * (13 + 2 * cells) <= 2 ^ (8 * mode.wordBytes)
@[expose] def registerAddress (mode : Mode) (base : Nat) (register : Dolan.Mov.Register) : Nat :=
  Layout.registerField mode base (Dolan.Four.slot register)
@[expose] def registerWord (mode : Mode) (base : Nat) (register : Dolan.Mov.Register) : Word mode :=
  Arithmetic.encodeNat mode (registerAddress mode base register)
@[expose] def heapIndex (pointer : Nat × Bool) : Nat := 13 + 2 * pointer.1 + if pointer.2 then 1 else 0
@[expose] def heapAddress (mode : Mode) (base : Nat) (pointer : Nat × Bool) : Nat :=
  Layout.heapField mode base pointer.1 pointer.2
@[expose] def heapWord (mode : Mode) (base : Nat) (pointer : Nat × Bool) : Word mode :=
  Arithmetic.encodeNat mode (heapAddress mode base pointer)

/-- Every source register and both words of each represented heap cell are
actual encoded operand fields. The finite domain is explicit. -/
structure Rep (mode : Mode) (base cells : Nat) (source : Dolan.Mov.State) (memory : ByteMemory.Memory) : Prop where
  registers : forall register, load mode memory (registerWord mode base register) = SourceValues.encodeWord mode base (source.registers register)
  heap : forall pointer : Nat × Bool, pointer.1 < cells ->
    load mode memory (heapWord mode base pointer) = SourceValues.encodeWord mode base (source.memory pointer)

theorem field_fits (mode : Mode) (base cells index : Nat) (capacity : Capacity mode base cells)
    (inside : index < 13 + 2 * cells) : Layout.fieldAddress mode base index < 2 ^ (8 * mode.wordBytes) := by
  have whole := Layout.finite_capacity mode base (13 + 2 * cells) index inside capacity
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  omega

theorem base_fits (mode : Mode) (base cells : Nat) (capacity : Capacity mode base cells) :
    base < 2 ^ (8 * mode.wordBytes) := by
  simpa only [Layout.fieldAddress, Nat.mul_zero, Nat.add_zero] using field_fits mode base cells 0 capacity (by omega)

theorem metadata_fits (mode : Mode) (base cells position : Nat) (capacity : Capacity mode base cells) (before : position < base) :
    position < 2 ^ (8 * mode.wordBytes) := Nat.lt_trans before (base_fits mode base cells capacity)

theorem register_fits (mode : Mode) (base cells : Nat) (register : Dolan.Mov.Register)
    (capacity : Capacity mode base cells) : registerAddress mode base register < 2 ^ (8 * mode.wordBytes) :=
  field_fits mode base cells (Dolan.Four.slot register).val capacity (by have small := (Dolan.Four.slot register).isLt; omega)

theorem heap_index_inside (cells : Nat) (pointer : Nat × Bool) (inside : pointer.1 < cells) :
    heapIndex pointer < 13 + 2 * cells := by
  cases second : pointer.2 <;> simp [heapIndex, second] <;> omega

theorem heap_fits (mode : Mode) (base cells : Nat) (pointer : Nat × Bool)
    (capacity : Capacity mode base cells) (inside : pointer.1 < cells) :
    heapAddress mode base pointer < 2 ^ (8 * mode.wordBytes) :=
  field_fits mode base cells (heapIndex pointer) capacity (heap_index_inside cells pointer inside)

theorem register_toNat (mode : Mode) (base cells : Nat) (register : Dolan.Mov.Register)
    (capacity : Capacity mode base cells) : (registerWord mode base register).toNat = registerAddress mode base register :=
  Arithmetic.encode_nat_toNat mode _ (register_fits mode base cells register capacity)

theorem heap_toNat (mode : Mode) (base cells : Nat) (pointer : Nat × Bool)
    (capacity : Capacity mode base cells) (inside : pointer.1 < cells) :
    (heapWord mode base pointer).toNat = heapAddress mode base pointer :=
  Arithmetic.encode_nat_toNat mode _ (heap_fits mode base cells pointer capacity inside)

theorem register_owned (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (origin base cells : Nat)
    (register : Dolan.Mov.Register) (capacity : Capacity mode base cells) :
    SpacedCombinedImage.Owned mode whole origin base (registerWord mode base register) :=
  Or.inr ⟨(Dolan.Four.slot register).val, register_toNat mode base cells register capacity⟩

theorem heap_owned (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (origin base cells : Nat)
    (pointer : Nat × Bool) (capacity : Capacity mode base cells) (inside : pointer.1 < cells) :
    SpacedCombinedImage.Owned mode whole origin base (heapWord mode base pointer) :=
  Or.inr ⟨heapIndex pointer, heap_toNat mode base cells pointer capacity inside⟩

theorem register_injective (mode : Mode) (base cells : Nat) (capacity : Capacity mode base cells) :
    Function.Injective (registerWord mode base) := by
  intro first second same
  have values := congrArg (fun value : Word mode => value.toNat) same
  rw [register_toNat mode base cells first capacity, register_toNat mode base cells second capacity] at values
  exact Dolan.Four.slot_injective (Fin.ext (Layout.field_address_injective mode base values))

theorem heap_address_injective (mode : Mode) (base : Nat) : Function.Injective (heapAddress mode base) := by
  intro first second same
  rcases first with ⟨firstCell, firstSide⟩
  rcases second with ⟨secondCell, secondSide⟩
  have indices : heapIndex (firstCell, firstSide) = heapIndex (secondCell, secondSide) :=
    Layout.field_address_injective mode base same
  cases firstSide <;> cases secondSide <;> dsimp [heapIndex] at indices
  all_goals first
    | exfalso; omega
    | have cells : firstCell = secondCell := by omega
      subst secondCell
      rfl

theorem heap_injective (mode : Mode) (base cells : Nat) (first second : Nat × Bool)
    (capacity : Capacity mode base cells) (firstInside : first.1 < cells) (secondInside : second.1 < cells)
    (same : heapWord mode base first = heapWord mode base second) : first = second := by
  apply heap_address_injective mode base
  have values := congrArg (fun value : Word mode => value.toNat) same
  rw [heap_toNat mode base cells first capacity firstInside, heap_toNat mode base cells second capacity secondInside] at values
  exact values

theorem register_heap_separate (mode : Mode) (base cells : Nat) (register : Dolan.Mov.Register) (pointer : Nat × Bool)
    (capacity : Capacity mode base cells) (inside : pointer.1 < cells) :
    Not (registerWord mode base register = heapWord mode base pointer) := by
  intro same
  have values := congrArg (fun value : Word mode => value.toNat) same
  rw [register_toNat mode base cells register capacity, heap_toNat mode base cells pointer capacity inside] at values
  have before := Layout.register_before_heap mode base (Dolan.Four.slot register)
  have high := Layout.heap_at_or_above_boundary mode base pointer.1 pointer.2
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  change Layout.registerField mode base (Dolan.Four.slot register) = Layout.heapField mode base pointer.1 pointer.2 at values
  omega

theorem field_not_before (mode : Mode) (base cells index position : Nat)
    (capacity : Capacity mode base cells) (inside : index < 13 + 2 * cells)
    (positionFits : position < 2 ^ (8 * mode.wordBytes)) (before : position < base) :
    Not (Arithmetic.encodeNat mode (Layout.fieldAddress mode base index) = Arithmetic.encodeNat mode position) := by
  intro same
  have values := congrArg (fun value : Word mode => value.toNat) same
  rw [Arithmetic.encode_nat_toNat mode _ (field_fits mode base cells index capacity inside), Arithmetic.encode_nat_toNat mode position positionFits] at values
  have above : base <= Layout.fieldAddress mode base index := Nat.le_add_right _ _
  omega

theorem register_not_before (mode : Mode) (base cells position : Nat) (register : Dolan.Mov.Register)
    (capacity : Capacity mode base cells) (positionFits : position < 2 ^ (8 * mode.wordBytes)) (before : position < base) :
    Not (registerWord mode base register = Arithmetic.encodeNat mode position) :=
  field_not_before mode base cells (Dolan.Four.slot register).val position capacity
    (by have small := (Dolan.Four.slot register).isLt; omega) positionFits before

theorem heap_not_before (mode : Mode) (base cells position : Nat) (pointer : Nat × Bool)
    (capacity : Capacity mode base cells) (inside : pointer.1 < cells)
    (positionFits : position < 2 ^ (8 * mode.wordBytes)) (before : position < base) :
    Not (heapWord mode base pointer = Arithmetic.encodeNat mode position) :=
  field_not_before mode base cells (heapIndex pointer) position capacity (heap_index_inside cells pointer inside) positionFits before

theorem boundary_fits (mode : Mode) (base cells : Nat) (capacity : Capacity mode base cells) (positive : 0 < cells) :
    Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes) :=
  field_fits mode base cells 13 capacity (by omega)

theorem value_fits (mode : Mode) (base cells : Nat) (value : Dolan.Mov.Word)
    (capacity : Capacity mode base cells) (positive : 0 < cells)
    (inside : match value with | .address cell => cell < cells | .offset _ => True) : SourceValues.Fits mode base value := by
  cases value with
  | address cell => exact heap_fits mode base cells (cell, false) capacity inside
  | offset choice => exact Nat.lt_trans (Arithmetic.offset_below_boundary mode base choice) (boundary_fits mode base cells capacity positive)

theorem address_fits (mode : Mode) (base cells : Nat) (value : Dolan.Mov.Word) (choice : Bool)
    (capacity : Capacity mode base cells)
    (inside : match value with | .address cell => cell < cells | .offset _ => True) : SourceValues.AddressFits mode base value choice := by
  cases value with
  | address cell => exact heap_fits mode base cells (cell, choice) capacity inside
  | offset _ => trivial

/-- Initial operand payloads use the generator's thirteen-register prefix and
two consecutive fields per source heap cell. -/
@[expose] def initialValues (mode : Mode) (base : Nat) (source : Dolan.Mov.State) (index : Nat) : Word mode :=
  if inside : index < 13 then SourceValues.encodeWord mode base (source.registers (Dolan.Four.registerAt ⟨index, inside⟩))
  else SourceValues.encodeWord mode base (source.memory ((index - 13) / 2, decide ((index - 13) % 2 = 1)))

theorem initial_register_value (mode : Mode) (base : Nat) (source : Dolan.Mov.State) (register : Dolan.Mov.Register) :
    initialValues mode base source (Dolan.Four.slot register).val = SourceValues.encodeWord mode base (source.registers register) := by
  simp [initialValues, (Dolan.Four.slot register).isLt, Dolan.Four.register_at_slot]

theorem initial_heap_value (mode : Mode) (base : Nat) (source : Dolan.Mov.State) (pointer : Nat × Bool) :
    initialValues mode base source (heapIndex pointer) = SourceValues.encodeWord mode base (source.memory pointer) := by
  have high : Not (heapIndex pointer < 13) := by unfold heapIndex; omega
  have cell : (heapIndex pointer - 13) / 2 = pointer.1 := by
    cases side : pointer.2 with
    | false => simp [heapIndex, side]
    | true =>
      simp [heapIndex, side]
      omega
  have side : decide ((heapIndex pointer - 13) % 2 = 1) = pointer.2 := by
    cases side : pointer.2 with
    | false => simp [heapIndex, side]
    | true =>
      have remainder : (heapIndex pointer - 13) % 2 = 1 := by
        simp [heapIndex, side]
        omega
      simp [remainder]
  rw [initialValues, dite_eq_right high, cell, side]

theorem initial_rep (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (origin base cells : Nat)
    (source : Dolan.Mov.State) (capacity : Capacity mode base cells)
    (enough : moffsOperandOffset mode <= base)
    (gap : origin + SpacedPacking.size mode whole <= base - moffsOperandOffset mode) :
    Rep mode base cells source (SpacedCombinedImage.image mode whole origin base (initialValues mode base source)) := by
  constructor
  · intro register
    change Protected.wordAt mode _ (registerWord mode base register).toNat = _
    rw [register_toNat mode base cells register capacity]
    change Protected.wordAt mode _ (Layout.fieldAddress mode base (Dolan.Four.slot register).val) = _
    rw [SpacedCombinedImage.initial_word mode whole origin base _ _ enough gap]
    exact initial_register_value mode base source register
  · intro pointer inside
    change Protected.wordAt mode _ (heapWord mode base pointer).toNat = _
    rw [heap_toNat mode base cells pointer capacity inside]
    change Protected.wordAt mode _ (Layout.fieldAddress mode base (heapIndex pointer)) = _
    rw [SpacedCombinedImage.initial_word mode whole origin base _ _ enough gap]
    exact initial_heap_value mode base source pointer

end SmcTuring.Native.SourceData

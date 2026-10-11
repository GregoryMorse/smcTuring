module
public import SmcTuring.SMC.VirtualRegisters

public section

namespace SmcTuring.SMC.Virtual

open Dolan

@[expose] def fieldIndex (layout : SMC.Layout) (address : Int) : Nat :=
  ((address - layout.base) / layout.stride).toNat

theorem field_index_correct (layout : SMC.Layout) (index : Nat) :
    fieldIndex layout (fieldAddress layout index) = index := by
  have positive := layout.stride_positive
  have nonzero : layout.stride ≠ 0 := by omega
  have difference : layout.base + layout.stride * (index : Int) - layout.base =
      layout.stride * (index : Int) := by omega
  simp only [fieldIndex, fieldAddress, difference, Int.mul_ediv_cancel_left _ nonzero]
  simp

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

@[expose] def dataState (layout : Layout) (source : Mov.State) : State :=
  { acc := 0, stack := 0, pc := 0, carry := false, memory := dataMemory layout source }

theorem data_state_correct (layout : Layout) (source : Mov.State) : Rep layout source (dataState layout source) := by
  constructor
  · intro r
    simp [dataState, dataMemory, registerField, field_index_correct, (Four.slot r).isLt, Four.register_at_slot]
  · rintro ⟨cell, choice⟩
    let index := layout.data.reserved + 2 * cell + (if choice then 1 else 0)
    have enough := layout.enoughRegisters
    have high : ¬ index < 13 := by dsimp [index]; split <;> omega
    have quotient : (index - layout.data.reserved) / 2 = cell := by dsimp [index]; split <;> omega
    have remainder : (index - layout.data.reserved) % 2 = if choice then 1 else 0 := by
      dsimp [index]
      split <;> omega
    have bit : decide ((index - layout.data.reserved) % 2 = 1) = choice := by
      rw [remainder]
      cases choice <;> rfl
    simp only [dataState, dataMemory, heapField, field_index_correct]
    change (if h : index < 13 then _ else _) = _
    simp only [high, ↓reduceDIte]
    change encodeWord layout.data (source.memory ((index - layout.data.reserved) / 2,
      decide ((index - layout.data.reserved) % 2 = 1))) = _
    rw [quotient, bit]

end SmcTuring.SMC.Virtual

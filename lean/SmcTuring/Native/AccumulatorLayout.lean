module
public import SmcTuring.Native.ConversionLayout

public section
namespace SmcTuring.Native.AccumulatorLayout
open Execution ControlImage

/-- Printed Listing 9: one entry store and three exit instructions.
Save/pointer denote complete full-width operand fields, not owner headers. -/
structure Layout where
  prologue : Nat
  epilogue : Nat
  save : Nat
  pointer : Nat

@[expose] def exchangeSize (mode : Mode) : Nat := instructionLength mode (.memory .exchangeAcc 0)
@[expose] def storeSize (mode : Mode) : Nat := match mode with | .x86 => 5 | .x64 => 7
@[expose] def savedPC (mode : Mode) (layout : Layout) : Nat := layout.prologue + storeSize mode
@[expose] def secondPC (mode : Mode) (layout : Layout) : Nat := layout.epilogue + exchangeSize mode
@[expose] def thirdPC (mode : Mode) (layout : Layout) : Nat := secondPC mode layout + storeSize mode
@[expose] def endPC (mode : Mode) (layout : Layout) : Nat := thirdPC mode layout + exchangeSize mode
@[expose] def entryDisp (mode : Mode) (layout : Layout) : BitVec 32 :=
  Relocation.memoryDisp mode (savedPC mode layout) layout.save
@[expose] def firstDisp (mode : Mode) (layout : Layout) : BitVec 32 :=
  Relocation.instructionDisp mode .exchangeAcc layout.epilogue layout.pointer
@[expose] def secondDisp (mode : Mode) (layout : Layout) : BitVec 32 :=
  Relocation.memoryDisp mode (thirdPC mode layout) layout.pointer
@[expose] def thirdDisp (mode : Mode) (layout : Layout) : BitVec 32 :=
  Relocation.instructionDisp mode .exchangeAcc (thirdPC mode layout) layout.save
@[expose] def saveForm (mode : Mode) (layout : Layout) : Form mode :=
  Reader.storeForm mode (Arithmetic.encodeNat mode layout.save) (entryDisp mode layout)
@[expose] def first (mode : Mode) (layout : Layout) : Form mode := .memory .exchangeAcc (firstDisp mode layout)
@[expose] def second (mode : Mode) (layout : Layout) : Form mode :=
  Reader.storeForm mode (Arithmetic.encodeNat mode layout.pointer) (secondDisp mode layout)
@[expose] def third (mode : Mode) (layout : Layout) : Form mode := .memory .exchangeAcc (thirdDisp mode layout)
@[expose] def program (mode : Mode) (layout : Layout) : List (Form mode) := [first mode layout, second mode layout, third mode layout]
@[expose] def entries (mode : Mode) (layout : Layout) : List (Entry mode) :=
  [⟨layout.prologue,.fixed (saveForm mode layout)⟩,⟨layout.epilogue,.fixed (first mode layout)⟩,
    ⟨secondPC mode layout,.fixed (second mode layout)⟩,⟨thirdPC mode layout,.fixed (third mode layout)⟩]

structure Admissible (mode : Mode) (layout : Layout) : Prop where
  prologueFits : savedPC mode layout < 2 ^ (8 * mode.wordBytes)
  epilogueFits : endPC mode layout < 2 ^ (8 * mode.wordBytes)
  saveFits : layout.save + mode.wordBytes ≤ 2 ^ (8 * mode.wordBytes)
  pointerFits : layout.pointer + mode.wordBytes ≤ 2 ^ (8 * mode.wordBytes)
  separate : layout.save + mode.wordBytes ≤ layout.pointer ∨ layout.pointer + mode.wordBytes ≤ layout.save
  entryRange : mode = .x64 → Relocation.SignedDelta (savedPC mode layout) layout.save
  firstRange : mode = .x64 → Relocation.SignedDelta (secondPC mode layout) layout.pointer
  secondRange : mode = .x64 → Relocation.SignedDelta (thirdPC mode layout) layout.pointer
  thirdRange : mode = .x64 → Relocation.SignedDelta (endPC mode layout) layout.save

theorem lengths (mode : Mode) (layout : Layout) :
    instructionLength mode (saveForm mode layout) = storeSize mode ∧
    instructionLength mode (first mode layout) = exchangeSize mode ∧
    instructionLength mode (second mode layout) = storeSize mode ∧
    instructionLength mode (third mode layout) = exchangeSize mode := by
  cases mode <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem save_toNat (mode : Mode) (layout : Layout) (valid : Admissible mode layout) :
    (Arithmetic.encodeNat mode layout.save).toNat = layout.save := by
  apply Arithmetic.encode_nat_toNat
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  have fits := valid.saveFits
  omega

theorem pointer_toNat (mode : Mode) (layout : Layout) (valid : Admissible mode layout) :
    (Arithmetic.encodeNat mode layout.pointer).toNat = layout.pointer := by
  apply Arithmetic.encode_nat_toNat
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  have fits := valid.pointerFits
  omega

theorem save_next (mode : Mode) (layout : Layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.prologue) :
    nextPC mode (saveForm mode layout) state = Arithmetic.encodeNat mode (savedPC mode layout) := by
  rw [Relocation.next_pc mode state _ _ entry,(lengths mode layout).1]
  rfl

theorem first_next (mode : Mode) (layout : Layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    nextPC mode (first mode layout) state = Arithmetic.encodeNat mode (secondPC mode layout) := by
  rw [Relocation.next_pc mode state _ _ entry,(lengths mode layout).2.1]
  rfl

theorem second_next (mode : Mode) (layout : Layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (secondPC mode layout)) :
    nextPC mode (second mode layout) state = Arithmetic.encodeNat mode (thirdPC mode layout) := by
  rw [Relocation.next_pc mode state _ _ entry,(lengths mode layout).2.2.1]
  rfl

theorem third_next (mode : Mode) (layout : Layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (thirdPC mode layout)) :
    nextPC mode (third mode layout) state = Arithmetic.encodeNat mode (endPC mode layout) := by
  rw [Relocation.next_pc mode state _ _ entry,(lengths mode layout).2.2.2]
  rfl

theorem save_hits (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.prologue) :
    Reader.storeAddress mode state (Arithmetic.encodeNat mode layout.save) (entryDisp mode layout) =
      Arithmetic.encodeNat mode layout.save := by
  cases mode with
  | x86 => rfl
  | x64 =>
    change memoryAddress .x64 (nextPC .x64 (saveForm .x64 layout) state) _ = _
    rw [save_next .x64 layout state entry]
    exact Relocation.memory_hits .x64 _ _ valid.entryRange

theorem first_hits (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    memoryAddress mode (nextPC mode (first mode layout) state) (firstDisp mode layout) =
      Arithmetic.encodeNat mode layout.pointer :=
  Relocation.instruction_memory_hits mode .exchangeAcc _ _ state entry valid.firstRange

theorem second_hits (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (secondPC mode layout)) :
    Reader.storeAddress mode state (Arithmetic.encodeNat mode layout.pointer) (secondDisp mode layout) =
      Arithmetic.encodeNat mode layout.pointer := by
  cases mode with
  | x86 => rfl
  | x64 =>
    change memoryAddress .x64 (nextPC .x64 (second .x64 layout) state) _ = _
    rw [second_next .x64 layout state entry]
    exact Relocation.memory_hits .x64 _ _ valid.secondRange

theorem third_hits (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (thirdPC mode layout)) :
    memoryAddress mode (nextPC mode (third mode layout) state) (thirdDisp mode layout) =
      Arithmetic.encodeNat mode layout.save :=
  Relocation.instruction_memory_hits mode .exchangeAcc _ _ state entry valid.thirdRange

theorem save_pointer_apart (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (index : Fin mode.wordBytes) :
    ¬ByteMemory.Inside layout.save mode.wordBytes (layout.pointer + index.val) := by
  have bound := index.isLt
  have separate := valid.separate
  unfold ByteMemory.Inside
  omega

end SmcTuring.Native.AccumulatorLayout

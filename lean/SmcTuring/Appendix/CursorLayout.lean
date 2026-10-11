module
public import SmcTuring.Native.MixedDword
public import SmcTuring.Native.MixedMemory
public import SmcTuring.Native.DwordLayout

public section
namespace SmcTuring.Appendix.CursorLayout
open Native
structure Layout where
  start : Nat
  cursor : Nat
  head : Nat
@[expose] def exchangeSize (mode : Mode) : Nat := instructionLength mode (.memory .exchangeAcc 0)
@[expose] def middlePC (mode : Mode) (layout : Layout) : Nat := layout.start+exchangeSize mode
@[expose] def lastPC (mode : Mode) (layout : Layout) : Nat := middlePC mode layout+7
@[expose] def endPC (mode : Mode) (layout : Layout) : Nat := lastPC mode layout+exchangeSize mode
@[expose] def firstDisp (mode : Mode) (layout : Layout) : BitVec 32 :=
  Relocation.memoryDisp mode (middlePC mode layout) layout.cursor
@[expose] def lastDisp (mode : Mode) (layout : Layout) : BitVec 32 :=
  Relocation.memoryDisp mode (endPC mode layout) layout.cursor
@[expose] def first (mode : Mode) (layout : Layout) : MixedDword.Form mode :=
  MixedDword.exchange mode (firstDisp mode layout)
@[expose] def middle (mode : Mode) (value : BitVec 32) : MixedDword.Form mode :=
  .arithmetic (.xorAtAccumulator value)
@[expose] def last (mode : Mode) (layout : Layout) : MixedDword.Form mode :=
  MixedDword.exchange mode (lastDisp mode layout)
@[expose] def program (mode : Mode) (layout : Layout) (value : BitVec 32) : List (MixedDword.Form mode) :=
  [first mode layout,middle mode value,last mode layout]

structure Valid (mode : Mode) (layout : Layout) : Prop where
  codeFits : endPC mode layout < 2^(8*mode.wordBytes)
  cursorFits : layout.cursor+mode.wordBytes ≤ 2^(8*mode.wordBytes)
  headFits : layout.head+10 ≤ 2^(8*mode.wordBytes)
  separate : layout.cursor+mode.wordBytes ≤ layout.head+6 ∨ layout.head+10 ≤ layout.cursor
  cursorOutside : layout.cursor+mode.wordBytes ≤ layout.start ∨ endPC mode layout ≤ layout.cursor
  tapeOutside : layout.head+10 ≤ layout.start ∨ endPC mode layout ≤ layout.head+6
  firstRange : mode = .x64 → Relocation.SignedDelta (middlePC mode layout) layout.cursor
  lastRange : mode = .x64 → Relocation.SignedDelta (endPC mode layout) layout.cursor

theorem exchange_sizes : exchangeSize .x86 = 6 ∧ exchangeSize .x64 = 7 := ⟨rfl,rfl⟩
theorem lengths (mode : Mode) (layout : Layout) (value : BitVec 32) :
    MixedDword.length mode (first mode layout) = exchangeSize mode ∧
    MixedDword.length mode (middle mode value) = 7 ∧
    MixedDword.length mode (last mode layout) = exchangeSize mode := by
  cases mode <;> exact ⟨rfl,rfl,rfl⟩
theorem endpoint (mode : Mode) (layout : Layout) :
    endPC mode layout = layout.start+2*exchangeSize mode+7 := by
  unfold endPC lastPC middlePC
  omega
theorem spans : 2*exchangeSize .x86+7=19 ∧ 2*exchangeSize .x64+7=21 := ⟨rfl,rfl⟩

theorem cursor_toNat (mode : Mode) (layout : Layout) (valid : Valid mode layout) :
    (Arithmetic.encodeNat mode layout.cursor).toNat = layout.cursor := by
  apply Arithmetic.encode_nat_toNat
  have fits := valid.cursorFits
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  omega
theorem head_toNat (mode : Mode) (layout : Layout) (valid : Valid mode layout) :
    (Arithmetic.encodeNat mode (layout.head+6)).toNat = layout.head+6 := by
  apply Arithmetic.encode_nat_toNat
  have fits := valid.headFits
  omega

theorem first_next (mode : Mode) (layout : Layout) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    Execution.nextPC mode (.memory .exchangeAcc (firstDisp mode layout)) state =
      Arithmetic.encodeNat mode (middlePC mode layout) := by
  rw [Relocation.next_pc mode state _ layout.start entry,
    Relocation.memory_length mode .exchangeAcc (firstDisp mode layout)]
  rfl

theorem last_next (mode : Mode) (layout : Layout) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (lastPC mode layout)) :
    Execution.nextPC mode (.memory .exchangeAcc (lastDisp mode layout)) state =
      Arithmetic.encodeNat mode (endPC mode layout) := by
  rw [Relocation.next_pc mode state _ _ entry,
    Relocation.memory_length mode .exchangeAcc (lastDisp mode layout)]
  rfl

theorem first_hits (mode : Mode) (layout : Layout) (valid : Valid mode layout) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    Execution.memoryAddress mode (Execution.nextPC mode (.memory .exchangeAcc (firstDisp mode layout)) state)
      (firstDisp mode layout) = Arithmetic.encodeNat mode layout.cursor := by
  rw [first_next mode layout state entry]
  exact Relocation.memory_hits mode _ _ valid.firstRange

theorem last_hits (mode : Mode) (layout : Layout) (valid : Valid mode layout) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (lastPC mode layout)) :
    Execution.memoryAddress mode (Execution.nextPC mode (.memory .exchangeAcc (lastDisp mode layout)) state)
      (lastDisp mode layout) = Arithmetic.encodeNat mode layout.cursor := by
  rw [last_next mode layout state entry]
  exact Relocation.memory_hits mode _ _ valid.lastRange

theorem cursor_apart (mode : Mode) (layout : Layout) (valid : Valid mode layout) (index : Fin mode.wordBytes) :
    ¬ByteMemory.Inside (layout.head+6) 4 (layout.cursor+index.val) := by
  have apart := valid.separate
  have bound := index.isLt
  unfold ByteMemory.Inside
  omega
theorem tape_apart (mode : Mode) (layout : Layout) (valid : Valid mode layout) (index : Fin 4) :
    ¬ByteMemory.Inside layout.cursor mode.wordBytes (layout.head+6+index.val) := by
  have apart := valid.separate
  have bound := index.isLt
  unfold ByteMemory.Inside
  omega


@[expose] def checks (mode : Mode) (layout : Layout) : List Bool :=
  [decide (endPC mode layout < 2^(8*mode.wordBytes)),
   decide (layout.cursor+mode.wordBytes ≤ 2^(8*mode.wordBytes)),
   decide (layout.head+10 ≤ 2^(8*mode.wordBytes)),
   decide (layout.cursor+mode.wordBytes ≤ layout.head+6 ∨ layout.head+10 ≤ layout.cursor),
   decide (layout.cursor+mode.wordBytes ≤ layout.start ∨ endPC mode layout ≤ layout.cursor),
   decide (layout.head+10 ≤ layout.start ∨ endPC mode layout ≤ layout.head+6),
   DwordLayout.reachable mode (middlePC mode layout) layout.cursor,
   DwordLayout.reachable mode (endPC mode layout) layout.cursor]

theorem checks_valid (mode : Mode) (layout : Layout) :
    (checks mode layout).all id = true ↔ Valid mode layout := by
  constructor
  · intro h
    simp only [checks,List.all_cons,List.all_nil,id_eq,Bool.and_eq_true,and_true,
      decide_eq_true_eq,DwordLayout.reachable_iff] at h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2⟩
  · intro valid
    simp only [checks,List.all_cons,List.all_nil,id_eq,Bool.and_eq_true,and_true,
      decide_eq_true_eq,DwordLayout.reachable_iff]
    exact ⟨valid.codeFits,valid.cursorFits,valid.headFits,valid.separate,
      valid.cursorOutside,valid.tapeOutside,valid.firstRange,valid.lastRange⟩

end SmcTuring.Appendix.CursorLayout

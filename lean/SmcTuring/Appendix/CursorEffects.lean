module
public import SmcTuring.Appendix.CursorLayout

public section
namespace SmcTuring.Appendix.CursorEffects
open Native CursorLayout MixedMemory
abbrev Dword := BitVec 32
@[expose] def delta (old fresh : Dword) (chosen : Bool) : Dword :=
  (old ^^^ fresh) &&& (if chosen then BitVec.allOnes 32 else 0)
theorem selection (old fresh : Dword) (chosen : Bool) :
    old ^^^ delta old fresh chosen = if chosen then fresh else old := by
  cases chosen with
  | false => simp [delta]
  | true =>
    change old ^^^ ((old ^^^ fresh) &&& BitVec.allOnes 32) = fresh
    rw [BitVec.and_allOnes,←BitVec.xor_assoc]
    simp

/-- Listing 8 copies the rule symbol, which need only equal the live tape
symbol when the comparison chooses the update. -/
theorem selection_rule (ruleOld tapeOld fresh : Dword) (chosen : Bool)
    (matching : chosen = true → ruleOld = tapeOld) :
    tapeOld ^^^ delta ruleOld fresh chosen = if chosen then fresh else tapeOld := by
  cases chosen with
  | false => simp [delta]
  | true =>
    have same : ruleOld = tapeOld := matching rfl
    rw [same]
    exact selection tapeOld fresh true

@[expose] def swapped (mode : Mode) (layout : Layout) (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (first mode layout) state
@[expose] def updated (mode : Mode) (layout : Layout) (value : Dword) (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (middle mode value) (swapped mode layout state)
@[expose] def finish (mode : Mode) (layout : Layout) (value : Dword) (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (last mode layout) (updated mode layout value state)

theorem swapped_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    swapped mode layout state =
      { state with
        pc := Arithmetic.encodeNat mode (middlePC mode layout)
        accumulator := getWord mode state.memory layout.cursor
        memory := ByteMemory.putWord mode state.memory layout.cursor state.accumulator } := by
  rw [swapped,first,MixedDword.exchange_execution]
  change { state with
    pc := Execution.nextPC mode (.memory .exchangeAcc (firstDisp mode layout)) state
    accumulator := Execution.load mode state.memory
      (Execution.memoryAddress mode (Execution.nextPC mode (.memory .exchangeAcc (firstDisp mode layout)) state) (firstDisp mode layout))
    memory := ByteMemory.putWord mode state.memory
      (Execution.memoryAddress mode (Execution.nextPC mode (.memory .exchangeAcc (firstDisp mode layout)) state) (firstDisp mode layout)).toNat state.accumulator } = _
  rw [first_hits mode layout valid state entry,first_next mode layout state entry,
    cursor_toNat mode layout valid,load_nat mode state.memory layout.cursor (by
      have bound:=valid.cursorFits
      have positive : 0 < mode.wordBytes := by cases mode <;> decide
      omega)]

theorem swapped_pc (mode : Mode) (layout : Layout) (valid : Valid mode layout) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    (swapped mode layout state).pc = Arithmetic.encodeNat mode (middlePC mode layout) := by
  rw [swapped_effect mode layout valid state entry]

theorem updated_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head) :
    updated mode layout value state =
      { state with
        pc := Arithmetic.encodeNat mode (lastPC mode layout)
        accumulator := Arithmetic.encodeNat mode layout.head
        carry := false
        memory := DwordCode.put (ByteMemory.putWord mode state.memory layout.cursor state.accumulator)
          (layout.head+6) (DwordCode.get state.memory (layout.head+6) ^^^ value) } := by
  rw [updated,swapped_effect mode layout valid state entry,cursor]
  unfold middle MixedDword.execute DwordArithmetic.execute DwordArithmetic.next
    DwordArithmetic.carry DwordArithmetic.value DwordArithmetic.prior DwordArithmetic.address
  simp only [DwordArithmetic.length,DwordArithmetic.result,DwordArithmetic.flag]
  rw [show Arithmetic.encodeNat mode layout.head+Arithmetic.encodeNat mode 6 =
      Arithmetic.encodeNat mode (layout.head+6) from BitVec.ofNat_add_ofNat _ _,
    head_toNat mode layout valid,dword_after_wide mode state.memory layout.cursor (layout.head+6)
      state.accumulator (tape_apart mode layout valid)]
  have pc : Arithmetic.encodeNat mode (middlePC mode layout)+Arithmetic.encodeNat mode 7 =
      Arithmetic.encodeNat mode (lastPC mode layout) := BitVec.ofNat_add_ofNat _ _
  rw [pc]

theorem updated_pc (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head) :
    (updated mode layout value state).pc = Arithmetic.encodeNat mode (lastPC mode layout) := by
  rw [updated_effect mode layout valid value state entry cursor]

theorem cursor_after_update (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head) :
    getWord mode (updated mode layout value state).memory layout.cursor = state.accumulator := by
  rw [updated_effect mode layout valid value state entry cursor]
  rw [wide_after_dword mode _ (layout.head+6) layout.cursor _ (cursor_apart mode layout valid),get_put]

theorem finish_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head) :
    finish mode layout value state =
      { state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        carry := false
        memory := DwordCode.put state.memory (layout.head+6) (DwordCode.get state.memory (layout.head+6) ^^^ value) } := by
  have location := updated_pc mode layout valid value state entry cursor
  have read := cursor_after_update mode layout valid value state entry cursor
  rw [finish,last,MixedDword.exchange_execution]
  change { updated mode layout value state with
    pc := Execution.nextPC mode (.memory .exchangeAcc (lastDisp mode layout)) (updated mode layout value state)
    accumulator := Execution.load mode (updated mode layout value state).memory
      (Execution.memoryAddress mode (Execution.nextPC mode (.memory .exchangeAcc (lastDisp mode layout)) (updated mode layout value state)) (lastDisp mode layout))
    memory := ByteMemory.putWord mode (updated mode layout value state).memory
      (Execution.memoryAddress mode (Execution.nextPC mode (.memory .exchangeAcc (lastDisp mode layout)) (updated mode layout value state)) (lastDisp mode layout)).toNat
      (updated mode layout value state).accumulator } = _
  rw [last_hits mode layout valid _ location,last_next mode layout _ location,cursor_toNat mode layout valid,
    load_nat mode (updated mode layout value state).memory layout.cursor (by
      have bound:=valid.cursorFits
      have positive : 0 < mode.wordBytes := by cases mode <;> decide
      omega),read,updated_effect mode layout valid value state entry cursor]
  have memory : ByteMemory.putWord mode
      (DwordCode.put (ByteMemory.putWord mode state.memory layout.cursor state.accumulator)
        (layout.head+6) (DwordCode.get state.memory (layout.head+6) ^^^ value))
      layout.cursor (Arithmetic.encodeNat mode layout.head) =
      DwordCode.put state.memory (layout.head+6) (DwordCode.get state.memory (layout.head+6) ^^^ value) := by
    rw [stores_commute mode state.memory layout.cursor (layout.head+6) state.accumulator _ valid.separate,
      Writes.put_word_overwrite]
    rw [←stores_commute mode state.memory layout.cursor (layout.head+6) (Arithmetic.encodeNat mode layout.head) _ valid.separate,
      ←cursor,put_get_back]
  rw [memory]

theorem selected_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword)
    (chosen : Bool) (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = old) :
    finish mode layout (delta old fresh chosen) state =
      { state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        carry := false
        memory := DwordCode.put state.memory (layout.head+6) (if chosen then fresh else old) } := by
  rw [finish_effect mode layout valid _ state entry cursor,tape,selection]

theorem selected_effect_rule (mode : Mode) (layout : Layout) (valid : Valid mode layout)
    (ruleOld tapeOld fresh : Dword) (chosen : Bool) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = tapeOld)
    (matching : chosen = true → ruleOld = tapeOld) :
    finish mode layout (delta ruleOld fresh chosen) state =
      { state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        carry := false
        memory := DwordCode.put state.memory (layout.head+6) (if chosen then fresh else tapeOld) } := by
  rw [finish_effect mode layout valid _ state entry cursor,tape,
    selection_rule ruleOld tapeOld fresh chosen matching]

theorem restored_cursor (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head) :
    getWord mode (finish mode layout value state).memory layout.cursor = getWord mode state.memory layout.cursor := by
  rw [finish_effect mode layout valid value state entry cursor]
  exact wide_after_dword mode _ _ _ _ (cursor_apart mode layout valid)

theorem frame (mode : Mode) (layout : Layout) (valid : Valid mode layout) (value : Dword)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (cursor : getWord mode state.memory layout.cursor = Arithmetic.encodeNat mode layout.head)
    (position : Nat) (outside : ¬ByteMemory.Inside (layout.head+6) 4 position) :
    (finish mode layout value state).memory position = state.memory position := by
  rw [finish_effect mode layout valid value state entry cursor]
  exact ByteMemory.put_frame _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using outside)

end SmcTuring.Appendix.CursorEffects

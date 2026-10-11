module
public import SmcTuring.Native.Writes

public section

namespace SmcTuring.Native.Reader

open Execution

/-- MASM's fixed accumulator store uses A3 in x86 and RIP-relative 89 in x64.
The fourth, self-addressed store always uses the explicit MOFFS encoding. -/
@[expose] def storeForm (mode : Mode) (label : Word mode) (displacement : BitVec 32) : Form mode :=
  match mode with
  | .x86 => .moffs label
  | .x64 => .memory .storeAcc displacement

@[expose] def storeAddress (mode : Mode) (state : State mode) (label : Word mode)
    (displacement : BitVec 32) : Word mode :=
  match mode with
  | .x86 => label
  | .x64 => memoryAddress .x64 (nextPC .x64 (.memory .storeAcc displacement) state) displacement

@[expose] def swapped (mode : Mode) (state : State mode) (firstDisp : BitVec 32) : State mode :=
  execute mode (.memory .exchangeAcc firstDisp) state

@[expose] def restored (mode : Mode) (state : State mode) (label : Word mode)
    (firstDisp secondDisp : BitVec 32) : State mode :=
  execute mode (storeForm mode label secondDisp) (swapped mode state firstDisp)

@[expose] def dereferenced (mode : Mode) (state : State mode) (label : Word mode)
    (firstDisp secondDisp : BitVec 32) : State mode :=
  execute mode .exchangeIndirect (restored mode state label firstDisp secondDisp)

@[expose] def finish (mode : Mode) (state : State mode) (label : Word mode)
    (firstDisp secondDisp : BitVec 32) : State mode :=
  execute mode (.moffs (load mode state.memory label)) (dereferenced mode state label firstDisp secondDisp)

theorem exchange_effect (mode : Mode) (state : State mode) (label : Word mode) (firstDisp : BitVec 32)
    (hits : memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp = label) :
    swapped mode state firstDisp =
      { state with pc := nextPC mode (.memory .exchangeAcc firstDisp) state, accumulator := load mode state.memory label, memory := ByteMemory.putWord mode state.memory label.toNat state.accumulator } := by
  simp only [swapped, execute, executeMemory, hits]

theorem store_effect (mode : Mode) (state : State mode) (label : Word mode) (secondDisp : BitVec 32)
    (hits : storeAddress mode state label secondDisp = label) :
    execute mode (storeForm mode label secondDisp) state =
      storeState mode state (nextPC mode (storeForm mode label secondDisp) state) label state.accumulator state.carry := by
  cases mode with
  | x86 => rfl
  | x64 =>
    change memoryAddress .x64 (nextPC .x64 (.memory .storeAcc secondDisp) state) secondDisp = label at hits
    change storeState .x64 state (nextPC .x64 (.memory .storeAcc secondDisp) state)
      (memoryAddress .x64 (nextPC .x64 (.memory .storeAcc secondDisp) state) secondDisp) state.accumulator state.carry = _
    rw [hits]
    rfl

/-- The first two operations restore every byte, for any initial accumulator. -/
theorem restored_memory (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32)
    (firstHits : memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp = label)
    (secondHits : storeAddress mode (swapped mode state firstDisp) label secondDisp = label) :
    (restored mode state label firstDisp secondDisp).memory = state.memory := by
  unfold restored
  rw [store_effect mode _ label secondDisp secondHits, exchange_effect mode state label firstDisp firstHits]
  change ByteMemory.putWord mode (ByteMemory.putWord mode state.memory label.toNat state.accumulator)
    label.toNat (load mode state.memory label) = state.memory
  rw [Writes.put_word_overwrite, Writes.put_word_back]

theorem restored_accumulator (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32)
    (firstHits : memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp = label)
    (secondHits : storeAddress mode (swapped mode state firstDisp) label secondDisp = label) :
    (restored mode state label firstDisp secondDisp).accumulator = load mode state.memory label := by
  unfold restored
  rw [store_effect mode _ label secondDisp secondHits, exchange_effect mode state label firstDisp firstHits]
  rfl

theorem dereferenced_memory (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32)
    (firstHits : memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp = label)
    (secondHits : storeAddress mode (swapped mode state firstDisp) label secondDisp = label) :
    (dereferenced mode state label firstDisp secondDisp).memory =
      ByteMemory.putWord mode state.memory (load mode state.memory label).toNat (load mode state.memory label) := by
  change ByteMemory.putWord mode (restored mode state label firstDisp secondDisp).memory
      (restored mode state label firstDisp secondDisp).accumulator.toNat
      (restored mode state label firstDisp secondDisp).accumulator = _
  rw [restored_memory mode state label firstDisp secondDisp firstHits secondHits,
    restored_accumulator mode state label firstDisp secondDisp firstHits secondHits]

theorem dereferenced_accumulator (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32)
    (firstHits : memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp = label)
    (secondHits : storeAddress mode (swapped mode state firstDisp) label secondDisp = label) :
    (dereferenced mode state label firstDisp secondDisp).accumulator =
      load mode state.memory (load mode state.memory label) := by
  change load mode (restored mode state label firstDisp secondDisp).memory
    (restored mode state label firstDisp secondDisp).accumulator = _
  rw [restored_memory mode state label firstDisp secondDisp firstHits secondHits,
    restored_accumulator mode state label firstDisp secondDisp firstHits secondHits]

/-- The repaired reader restores the whole byte-memory function, including
pointer/label aliases. Live packet validity is established separately below. -/
theorem finish_memory (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32)
    (firstHits : memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp = label)
    (secondHits : storeAddress mode (swapped mode state firstDisp) label secondDisp = label) :
    (finish mode state label firstDisp secondDisp).memory = state.memory := by
  change ByteMemory.putWord mode (dereferenced mode state label firstDisp secondDisp).memory
    (load mode state.memory label).toNat (dereferenced mode state label firstDisp secondDisp).accumulator = _
  rw [dereferenced_memory mode state label firstDisp secondDisp firstHits secondHits,
    dereferenced_accumulator mode state label firstDisp secondDisp firstHits secondHits,
    Writes.put_word_overwrite, Writes.put_word_back]

theorem finish_accumulator (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32)
    (firstHits : memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp = label)
    (secondHits : storeAddress mode (swapped mode state firstDisp) label secondDisp = label) :
    (finish mode state label firstDisp secondDisp).accumulator = load mode state.memory (load mode state.memory label) :=
  dereferenced_accumulator mode state label firstDisp secondDisp firstHits secondHits

theorem finish_stack (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32) :
    (finish mode state label firstDisp secondDisp).stack = state.stack := by cases mode <;> rfl

theorem finish_carry (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32) :
    (finish mode state label firstDisp secondDisp).carry = state.carry := by cases mode <;> rfl

/-- The final MOFFS packet remains live after the indirect exchange when its
target is its own operand field or is separate from the complete packet.
Arbitrary partial byte overlap is deliberately not treated as safe fetch. -/
theorem fetch_last (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32)
    (firstHits : memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp = label)
    (secondHits : storeAddress mode (swapped mode state firstDisp) label secondDisp = label)
    (current : ByteMemory.bytesAt state.memory (dereferenced mode state label firstDisp secondDisp).pc.toNat
      (encode mode (.moffs (load mode state.memory label))).length = encode mode (.moffs (load mode state.memory label)))
    (safe : Or ((load mode state.memory label) = label)
      (forall index : Fin (encode mode (.moffs (load mode state.memory label))).length,
        Not (ByteMemory.Inside (load mode state.memory label).toNat mode.wordBytes
          ((dereferenced mode state label firstDisp secondDisp).pc.toNat + index.val)))) :
    Fetch.fetch mode (dereferenced mode state label firstDisp secondDisp).memory
      (dereferenced mode state label firstDisp secondDisp).pc.toNat = some (.moffs (load mode state.memory label)) := by
  apply Fetch.fetch_current_encoding
  rw [dereferenced_memory mode state label firstDisp secondDisp firstHits secondHits]
  rcases safe with same | separate
  · have selfLoad : load mode state.memory (load mode state.memory label) = load mode state.memory label := by
      rw [same]
      exact same
    have unchanged : ByteMemory.putWord mode state.memory (load mode state.memory label).toNat
        (load mode state.memory label) = state.memory := by
      calc
        _ = ByteMemory.putWord mode state.memory (load mode state.memory label).toNat
            (load mode state.memory (load mode state.memory label)) :=
          congrArg (ByteMemory.putWord mode state.memory (load mode state.memory label).toNat) selfLoad.symm
        _ = state.memory := Writes.put_word_back mode state.memory _
    rw [unchanged]
    exact current
  · have framed := ByteMemory.bytes_at_frame state.memory (load mode state.memory label).toNat
      (LittleEndian.wordEncode mode.wordBytes (load mode state.memory label))
      (dereferenced mode state label firstDisp secondDisp).pc.toNat
      (encode mode (.moffs (load mode state.memory label))).length (by simpa using separate)
    simpa only [ByteMemory.putWord] using framed.trans current

theorem store_write_address (mode : Mode) (state : State mode) (label : Word mode) (displacement : BitVec 32)
    (hits : storeAddress mode state label displacement = label) :
    Writes.address mode (storeForm mode label displacement) state = label := by
  cases mode with
  | x86 => rfl
  | x64 => exact hits

/-- All four actual write destinations are code operand fields whenever the
label and its loaded pointer are owned. Writes remain nonempty even on restore. -/
theorem four_writes_owned (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32)
    (firstHits : memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp = label)
    (secondHits : storeAddress mode (swapped mode state firstDisp) label secondDisp = label)
    (owned : Word mode -> Prop) (labelOwned : owned label) (pointerOwned : owned (load mode state.memory label)) :
    And (owned (Writes.address mode (.memory .exchangeAcc firstDisp) state))
      (And (owned (Writes.address mode (storeForm mode label secondDisp) (swapped mode state firstDisp)))
        (And (owned (Writes.address mode .exchangeIndirect (restored mode state label firstDisp secondDisp)))
          (owned (Writes.address mode (.moffs (load mode state.memory label)) (dereferenced mode state label firstDisp secondDisp))))) := by
  constructor
  · change owned (memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp)
    rw [firstHits]
    exact labelOwned
  · constructor
    · rw [store_write_address mode _ label secondDisp secondHits]
      exact labelOwned
    · constructor
      · change owned (restored mode state label firstDisp secondDisp).accumulator
        rw [restored_accumulator mode state label firstDisp secondDisp firstHits secondHits]
        exact pointerOwned
      · exact pointerOwned

/-- The first three selected encodings occupy the exact lengths recorded by
the assembler, before the final MOFFS opcode and mutable address field. -/
theorem prefix_length (mode : Mode) (label : Word mode) (firstDisp secondDisp : BitVec 32) :
    instructionLength mode (.memory .exchangeAcc firstDisp) +
      instructionLength mode (storeForm mode label secondDisp) +
      instructionLength mode .exchangeIndirect = (match mode with | .x86 => 13 | .x64 => 17) := by
  cases mode <;> rfl

theorem operand_offset (mode : Mode) (label : Word mode) (firstDisp secondDisp : BitVec 32) :
    instructionLength mode (.memory .exchangeAcc firstDisp) +
      instructionLength mode (storeForm mode label secondDisp) +
      instructionLength mode .exchangeIndirect + moffsOperandOffset mode =
        (match mode with | .x86 => 14 | .x64 => 19) := by cases mode <;> rfl

/-- Four live automatic fetches form the actual selected reader trace. -/
theorem trace_of_fetches (mode : Mode) (state : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32)
    (firstFetched : Fetch.fetch mode state.memory state.pc.toNat = some (.memory .exchangeAcc firstDisp))
    (secondFetched : Fetch.fetch mode (swapped mode state firstDisp).memory
      (swapped mode state firstDisp).pc.toNat = some (storeForm mode label secondDisp))
    (thirdFetched : Fetch.fetch mode (restored mode state label firstDisp secondDisp).memory
      (restored mode state label firstDisp secondDisp).pc.toNat = some .exchangeIndirect)
    (lastFetched : Fetch.fetch mode (dereferenced mode state label firstDisp secondDisp).memory
      (dereferenced mode state label firstDisp secondDisp).pc.toNat = some (.moffs (load mode state.memory label))) :
    Fetch.Trace mode state
      [.memory .exchangeAcc firstDisp, storeForm mode label secondDisp, .exchangeIndirect,
        .moffs (load mode state.memory label)] (finish mode state label firstDisp secondDisp) :=
  .step firstFetched (.step secondFetched (.step thirdFetched (.step lastFetched (.nil _))))

/-- The complete byte-restoration and accumulator result applies to any actual
automatic-fetch reader trace satisfying the two resolved operand addresses. -/
theorem trace_result (mode : Mode) (state result : State mode) (label : Word mode) (firstDisp secondDisp : BitVec 32)
    (firstHits : memoryAddress mode (nextPC mode (.memory .exchangeAcc firstDisp) state) firstDisp = label)
    (secondHits : storeAddress mode (swapped mode state firstDisp) label secondDisp = label)
    (trace : Fetch.Trace mode state
      [.memory .exchangeAcc firstDisp, storeForm mode label secondDisp, .exchangeIndirect,
        .moffs (load mode state.memory label)] result) :
    And (result.memory = state.memory)
      (And (result.accumulator = load mode state.memory (load mode state.memory label))
        (And (result.stack = state.stack) (result.carry = state.carry))) := by
  have effect := Fetch.trace_run_eq mode trace
  change result = finish mode state label firstDisp secondDisp at effect
  rw [effect]
  exact And.intro (finish_memory mode state label firstDisp secondDisp firstHits secondHits)
    (And.intro (finish_accumulator mode state label firstDisp secondDisp firstHits secondHits)
      (And.intro (finish_stack mode state label firstDisp secondDisp)
        (finish_carry mode state label firstDisp secondDisp)))

end SmcTuring.Native.Reader

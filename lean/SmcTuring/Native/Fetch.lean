module
public import SmcTuring.Native.Execution

public section

namespace SmcTuring.Native.Fetch

open LittleEndian

/-- The length classifier reads the selected core opcode and ModR/M only.
The exact decoder subsequently validates the complete payload and SBB's zero.
No address or displacement value contributes to the inferred packet length. -/
@[expose] def coreLength (mode : Mode) (opcode : Byte) (rest : List Byte) : Option Nat :=
  if opcode = 0xA3 then some ((wordPrefix mode).length + 1 + mode.wordBytes)
  else match rest with
    | [] => none
    | modrm :: _ =>
      if opcode = 0x87 && modrm = 0x00 then some ((wordPrefix mode).length + 2)
      else (operationOfTag opcode modrm).bind fun operation =>
        if operation = .callIndirect then none
        else some ((operation.prefix mode).length + 6 + operation.trailer.length)

/-- Restricted opcode-derived length, with near CALL handled before REX.W.
Unsupported encodings have no selected packet; this is not a general x86 decoder. -/
@[expose] def lengthOfBytes (mode : Mode) : List Byte -> Option Nat
  | [] => none
  | opcode :: rest =>
    if opcode = 0xE8 then some 5
    else if opcode = 0xFF then match rest with
      | modrm :: _ => if modrm = 0x15 then some 6 else none
      | [] => none
    else match mode with
      | .x86 => coreLength .x86 opcode rest
      | .x64 => if opcode = 0x48 then match rest with
          | core :: payload => coreLength .x64 core payload
          | [] => none
        else none

/-- Every selected encoding determines its own length, regardless of subsequent
instruction bytes. In particular, mutable operand bytes cannot choose a length. -/
theorem encoded_length (mode : Mode) (form : Form mode) (trailing : List Byte) :
    lengthOfBytes mode (encode mode form ++ trailing) = some (instructionLength mode form) := by
  cases form with
  | moffs address => cases mode <;> simp [lengthOfBytes, coreLength, encode, wordPrefix, instructionLength]
  | memory operation displacement =>
    cases mode <;> cases operation <;>
      simp [lengthOfBytes, coreLength, encode, wordPrefix, instructionLength,
        MemoryOp.prefix, MemoryOp.tag, MemoryOp.trailer, operationOfTag]
  | exchangeIndirect => cases mode <;> rfl
  | callRelative displacement => cases mode <;> rfl

/-- The classifier depends on at most the first three current bytes. -/
theorem length_take_three (mode : Mode) (bytes : List Byte) :
    lengthOfBytes mode (bytes.take 3) = lengthOfBytes mode bytes := by
  cases bytes with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil => rfl
    | cons second tail =>
      cases tail with
      | nil => rfl
      | cons third trailing => cases mode <;> simp [lengthOfBytes, coreLength]

/-- A shorter current-memory window is exactly the corresponding prefix. -/
theorem bytes_at_take (memory : ByteMemory.Memory) (pc count smaller : Nat)
    (bounded : smaller <= count) :
    (ByteMemory.bytesAt memory pc count).take smaller = ByteMemory.bytesAt memory pc smaller := by
  apply List.ext_getElem
  case hl => simp [bounded]
  case h => intro index left right; simp [ByteMemory.bytesAt]

/-- The selected current packet is taken after classifying its live header.
The 15-byte window is only a proof device; the classifier uses three bytes. -/
@[expose] def fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : Option (Form mode) :=
  (lengthOfBytes mode (ByteMemory.bytesAt memory pc 3)).bind fun length =>
    decode mode (ByteMemory.bytesAt memory pc length)

/-- Automatic fetch obtains the full packet from current memory after deriving
its length from its header, rather than taking a form or length as input. -/
theorem fetch_current_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : Form mode)
    (current : ByteMemory.bytesAt memory pc (encode mode form).length = encode mode form) :
    fetch mode memory pc = some form := by
  have bound : (encode mode form).length <= 15 := by
    rw [instruction_length]
    exact instruction_length_bound mode form
  have prefixWindow : (ByteMemory.bytesAt memory pc 15).take (encode mode form).length = encode mode form := by
    rw [bytes_at_take memory pc 15 _ bound, current]
  have window : ByteMemory.bytesAt memory pc 15 =
      encode mode form ++ (ByteMemory.bytesAt memory pc 15).drop (encode mode form).length := by
    calc
      ByteMemory.bytesAt memory pc 15 =
          (ByteMemory.bytesAt memory pc 15).take (encode mode form).length ++
            (ByteMemory.bytesAt memory pc 15).drop (encode mode form).length :=
        (List.take_append_drop _ _).symm
      _ = encode mode form ++ (ByteMemory.bytesAt memory pc 15).drop (encode mode form).length :=
        congrArg (fun leading => leading ++ (ByteMemory.bytesAt memory pc 15).drop (encode mode form).length) prefixWindow
  have length : lengthOfBytes mode (ByteMemory.bytesAt memory pc 3) = some (instructionLength mode form) := by
    rw [<-bytes_at_take memory pc 15 3 (by omega), length_take_three, window, encoded_length]
  unfold fetch
  rw [length, Option.bind_some, <-instruction_length, current, form_roundtrip]

theorem fetch_written_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : Form mode) :
    fetch mode (ByteMemory.putBytes memory pc (encode mode form)) pc = some form :=
  fetch_current_encoding mode _ pc form (ByteMemory.bytes_at_put memory pc (encode mode form))

/-- MOFFS patches are consumed by the automatic opcode-derived fetch. -/
theorem fetch_patched_moffs (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (old fresh : Word mode) :
    fetch mode
      (ByteMemory.putWord mode (ByteMemory.putBytes memory pc (encode mode (.moffs old)))
        (pc + moffsOperandOffset mode) fresh) pc = some (.moffs fresh) := by
  rw [ByteMemory.moffs_patch]
  exact fetch_written_encoding mode memory pc (.moffs fresh)

@[expose] def step (mode : Mode) (state : Execution.State mode) : Option (Execution.State mode) :=
  (fetch mode state.memory state.pc.toNat).map (fun form => Execution.execute mode form state)

theorem step_current_encoding (mode : Mode) (state : Execution.State mode) (form : Form mode)
    (current : ByteMemory.bytesAt state.memory state.pc.toNat (encode mode form).length = encode mode form) :
    step mode state = some (Execution.execute mode form state) := by
  simp only [step, fetch_current_encoding mode state.memory state.pc.toNat form current, Option.map_some]

theorem step_patched_moffs (mode : Mode) (state : Execution.State mode) (old fresh : Word mode) :
    let patched : Execution.State mode := { state with memory := ByteMemory.putWord mode (ByteMemory.putBytes state.memory state.pc.toNat (encode mode (.moffs old))) (state.pc.toNat + moffsOperandOffset mode) fresh }
    step mode patched = some (Execution.execute mode (.moffs fresh) patched) := by
  simp only [step, fetch_patched_moffs, Option.map_some]

/-- Each event's form is determined by the current byte memory and PC. -/
inductive Trace (mode : Mode) : Execution.State mode -> List (Form mode) -> Execution.State mode -> Prop where
  | nil (state : Execution.State mode) : Trace mode state [] state
  | step {state finish : Execution.State mode} {form : Form mode} {rest : List (Form mode)}
      (fetched : fetch mode state.memory state.pc.toNat = some form)
      (tail : Trace mode (Execution.execute mode form state) rest finish) : Trace mode state (form :: rest) finish

theorem trace_run_eq (mode : Mode) {state finish : Execution.State mode} {forms : List (Form mode)}
    (trace : Trace mode state forms finish) : finish = Execution.runForms mode forms state := by
  induction trace with
  | nil => rfl
  | step fetched tail ih => exact ih

/-- Live packet traces compose at their actual common state. -/
theorem trace_append (mode : Mode) {state middle finish : Execution.State mode}
    {first second : List (Form mode)} (leading : Trace mode state first middle)
    (trailing : Trace mode middle second finish) : Trace mode state (first ++ second) finish := by
  induction leading with
  | nil => exact trailing
  | step fetched tail ih => exact .step fetched (ih trailing)

theorem trace_preserves_carry (mode : Mode) {state finish : Execution.State mode} {forms : List (Form mode)}
    (trace : Trace mode state forms finish)
    (preserves : forall form, List.Mem form forms -> Execution.CarryPreserving form) :
    finish.carry = state.carry := by
  rw [trace_run_eq mode trace]
  exact Execution.run_preserves_carry mode forms state preserves

/-- The first actual transition of a nonempty trace is automatic byte fetch,
not an instruction form supplied to the evaluator from outside memory. -/
theorem trace_head_step (mode : Mode) {state finish : Execution.State mode}
    {form : Form mode} {rest : List (Form mode)} (trace : Trace mode state (form :: rest) finish) :
    step mode state = some (Execution.execute mode form state) := by
  cases trace with
  | step fetched tail => simp only [step, fetched, Option.map_some]

/-- The incoming CF survives an automatically decoded ordinary MOV/XCHG/CALL. -/
theorem step_preserves_carry (mode : Mode) (state : Execution.State mode) (form : Form mode)
    (fetched : fetch mode state.memory state.pc.toNat = some form)
    (preserves : Execution.CarryPreserving form) :
    (step mode state).map Execution.State.carry = some state.carry := by
  simp only [step, fetched, Option.map_some, Execution.execute_preserves_carry mode form state preserves]

/-- The earlier SUB borrow reaches the SBB mask through automatic-fetch
reader/near-CALL bridges. The mask must have been initialized to zero. -/
theorem sub_bridge_sbb_mask (mode : Mode) (state finish : Execution.State mode)
    (subDisp sbbDisp : BitVec 32) (forms : List (Form mode))
    (bridge : Trace mode (Execution.execute mode (.memory .subtract subDisp) state) forms finish)
    (preserves : forall form, List.Mem form forms -> Execution.CarryPreserving form)
    (zero : Execution.load mode finish.memory
      (Execution.memoryAddress mode (Execution.nextPC mode (.memory .subtractBorrowZero sbbDisp) finish) sbbDisp) = 0) :
    Execution.load mode (Execution.execute mode (.memory .subtractBorrowZero sbbDisp) finish).memory
      (Execution.memoryAddress mode (Execution.nextPC mode (.memory .subtractBorrowZero sbbDisp) finish) sbbDisp) =
      Arithmetic.sbbZero mode (Arithmetic.unsignedBorrow
        (Execution.load mode state.memory
          (Execution.memoryAddress mode (Execution.nextPC mode (.memory .subtract subDisp) state) subDisp))
        state.accumulator) := by
  rw [Execution.sbb_zero_result mode finish sbbDisp zero, trace_preserves_carry mode bridge preserves,
    Execution.subtract_carry]

end SmcTuring.Native.Fetch

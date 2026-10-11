module
public import SmcTuring.Native.StringWindow
public import SmcTuring.Native.ReaderImage

public section
namespace SmcTuring.Native.StringInit
open StringExecution LittleEndian

@[expose] def field (mode : Mode) (start : Nat) : Nat := start+StringCodec.fieldOffset mode
@[expose] def first (start : Nat) : BitVec 32 := Relocation.instructionDisp .x64 .exchangeAcc start (field .x64 start)
@[expose] def second (start : Nat) : BitVec 32 := Relocation.instructionDisp .x64 .storeAcc (start+7) (field .x64 start)
@[expose] def forms (mode : Mode) (start initial : Nat) : List (StringForm.Form mode) :=
  match mode with
  | .x86 => [.initialize32 (BitVec.ofNat 32 (field .x86 start)) (BitVec.ofNat 32 initial)]
  | .x64 => [.native (.memory .exchangeAcc (first start)),.native (.memory .storeAcc (second start)),
      .native .exchangeIndirect,.native (.moffs (Arithmetic.encodeNat .x64 initial))]
@[expose] def leading (mode : Mode) (start : Nat) : List Byte :=
  match mode with
  | .x86 => [0xC7,0x05]++wordEncode 4 (BitVec.ofNat 32 (field .x86 start))
  | .x64 => Native.encode .x64 (.memory .exchangeAcc (first start))++Native.encode .x64 (.memory .storeAcc (second start))++
      Native.encode .x64 .exchangeIndirect++[0x48,0xA3]
@[expose] def bytes (mode : Mode) (start initial : Nat) : List Byte :=
  StringCodec.initialBytes mode start (field mode start) initial
@[expose] def accumulator (mode : Mode) (initial : Nat) (state : State mode) : Word mode :=
  match mode with
  | .x86 => state.principal.accumulator
  | .x64 => Execution.load .x64 state.principal.memory (Arithmetic.encodeNat .x64 initial)

theorem first_displacement (start : Nat) : first start = 12 := by
  have amount : Relocation.delta (start+7) (start+19) = 12 := by unfold Relocation.delta; omega
  unfold first Relocation.instructionDisp Relocation.memoryDisp Relocation.relative32 field
  change BitVec.ofInt 32 (Relocation.delta (start+7) (start+19)) = 12
  rw [amount]
  rfl

theorem second_displacement (start : Nat) : second start = 5 := by
  have amount : Relocation.delta (start+7+7) (start+19) = 5 := by unfold Relocation.delta; omega
  unfold second Relocation.instructionDisp Relocation.memoryDisp Relocation.relative32 field
  change BitVec.ofInt 32 (Relocation.delta (start+7+7) (start+19)) = 5
  rw [amount]
  rfl

theorem leading_length (mode : Mode) (start : Nat) : (leading mode start).length = StringCodec.fieldOffset mode := by
  cases mode <;> simp [leading,StringCodec.fieldOffset,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix]

theorem initial_shape (mode : Mode) (start initial : Nat) :
    bytes mode start initial = leading mode start++wordEncode mode.wordBytes (Arithmetic.encodeNat mode initial) := by
  cases mode <;> simp [bytes,leading,StringCodec.initialBytes,Appendix.ByteCode.encode,Appendix.ByteCode.ImmediateOp.tag,
    first,second,field,Mode.wordBytes,Native.encode,wordPrefix,List.append_assoc,Arithmetic.encodeNat]

theorem forms_encoding (mode : Mode) (start initial : Nat) :
    ((forms mode start initial).map (StringForm.encode mode)).flatten = bytes mode start initial := by
  cases mode <;> simp [forms,bytes,StringForm.encode,StringCodec.initialBytes,first,second,List.append_assoc]

theorem initialized_pointer (mode : Mode) (start initial : Nat) (memory : ByteMemory.Memory)
    (fits : start+StringCodec.initialSize mode < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt memory start (StringCodec.initialSize mode) = bytes mode start initial) :
    Execution.load mode memory (Arithmetic.encodeNat mode (field mode start)) = Arithmetic.encodeNat mode initial := by
  have fieldFits : field mode start < 2^(8*mode.wordBytes) := by
    cases mode <;> simp [field,StringCodec.fieldOffset,StringCodec.initialSize,Mode.wordBytes] at * <;> omega
  apply StringWindow.initial_word mode memory _ _ fieldFits
  have shape : ByteMemory.bytesAt memory start (leading mode start++wordEncode mode.wordBytes (Arithmetic.encodeNat mode initial)++[]).length =
      leading mode start++wordEncode mode.wordBytes (Arithmetic.encodeNat mode initial)++[] := by
    simp only [List.append_nil]
    rw [←initial_shape,bytes,StringCodec.initial_length]
    exact current
  have payload := StringWindow.packet_window memory start (leading mode start) (wordEncode mode.wordBytes (Arithmetic.encodeNat mode initial)) [] shape
  rw [leading_length,word_encode_length] at payload
  exact payload

theorem native_run (mode : Mode) (nativeForms : List (Native.Form mode)) (state : State mode) :
    run mode (nativeForms.map StringForm.Form.native) state = {state with principal := Execution.runForms mode nativeForms state.principal} := by
  induction nativeForms generalizing state with
  | nil => rfl
  | cons form rest ih =>
    change run mode (rest.map StringForm.Form.native) (execute mode (.native form) state) = _
    rw [ih]
    rfl

/-- Both printed DEFDATA initializers restore every byte. x86 preserves AX;
x64 has the actual repaired-reader accumulator result. Full SI/DI/SP/CF/DF
are retained. The payload pointer is read from the initial bytes. -/
theorem effect (mode : Mode) (start initial : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode start)
    (fits : start+StringCodec.initialSize mode < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode) = bytes mode start initial) :
    run mode (forms mode start initial) state = { state with principal := {state.principal with
      pc := Arithmetic.encodeNat mode (start+StringCodec.initialSize mode)
      accumulator := accumulator mode initial state} } := by
  have pointer := initialized_pointer mode start initial state.principal.memory fits current
  cases mode with
  | x86 =>
    have fieldFits : field .x86 start < 2^32 := by
      simp [field,StringCodec.fieldOffset,StringCodec.initialSize,Mode.wordBytes] at *; omega
    have unchanged : ByteMemory.putWord .x86 state.principal.memory (field .x86 start) (Arithmetic.encodeNat .x86 initial) = state.principal.memory := by
      rw [←pointer]
      have back := Writes.put_word_back .x86 state.principal.memory (Arithmetic.encodeNat .x86 (field .x86 start))
      rw [Arithmetic.encode_nat_toNat .x86 _ fieldFits] at back
      exact back
    change { state with
      principal := { state.principal with
        pc := state.principal.pc+Arithmetic.encodeNat .x86 10
        memory := ByteMemory.putWord .x86 state.principal.memory (BitVec.ofNat 32 (field .x86 start)).toNat (Arithmetic.encodeNat .x86 initial) } } = _
    rw [show (BitVec.ofNat 32 (field .x86 start)).toNat = field .x86 start from Arithmetic.encode_nat_toNat .x86 _ fieldFits,unchanged,location]
    have next : Arithmetic.encodeNat .x86 start+Arithmetic.encodeNat .x86 10 = Arithmetic.encodeNat .x86 (start+10) := BitVec.ofNat_add_ofNat _ _
    rw [next]
    rfl
  | x64 =>
    have readerPointer : Execution.load .x64 state.principal.memory (ReaderImage.label .x64 start) = Arithmetic.encodeNat .x64 initial := pointer
    have firstHits := ReaderImage.first_hits .x64 start state.principal location
    have secondHits := ReaderImage.second_hits .x64 start state.principal location
    have native : forms .x64 start initial =
        ([.memory .exchangeAcc (ReaderImage.firstDisp .x64 start),Reader.storeForm .x64 (ReaderImage.label .x64 start) (ReaderImage.secondDisp .x64),
          .exchangeIndirect,.moffs (Execution.load .x64 state.principal.memory (ReaderImage.label .x64 start))].map StringForm.Form.native) := by
      simp [forms,first_displacement,second_displacement,ReaderImage.firstDisp,ReaderImage.secondDisp,Reader.storeForm,readerPointer]
    rw [native,native_run]
    change {state with principal := Reader.finish .x64 state.principal (ReaderImage.label .x64 start) (ReaderImage.firstDisp .x64 start) (ReaderImage.secondDisp .x64)} = _
    have pc := ReaderImage.finish_pc .x64 start state.principal location
    have mem := Reader.finish_memory .x64 state.principal _ _ _ firstHits secondHits
    have ax := Reader.finish_accumulator .x64 state.principal _ _ _ firstHits secondHits
    have sp := Reader.finish_stack .x64 state.principal (ReaderImage.label .x64 start) (ReaderImage.firstDisp .x64 start) (ReaderImage.secondDisp .x64)
    have cf := Reader.finish_carry .x64 state.principal (ReaderImage.label .x64 start) (ReaderImage.firstDisp .x64 start) (ReaderImage.secondDisp .x64)
    have principal : Reader.finish .x64 state.principal (ReaderImage.label .x64 start) (ReaderImage.firstDisp .x64 start) (ReaderImage.secondDisp .x64) =
        {state.principal with pc := Arithmetic.encodeNat .x64 (start+27),accumulator := Execution.load .x64 state.principal.memory (Arithmetic.encodeNat .x64 initial)} := by
      cases finished : Reader.finish .x64 state.principal (ReaderImage.label .x64 start) (ReaderImage.firstDisp .x64 start) (ReaderImage.secondDisp .x64)
      simp only [finished] at pc mem ax sp cf
      rw [readerPointer] at ax
      simp only [ReaderImage.totalSize] at pc
      simp only [pc,mem,ax,sp,cf]
    rw [principal]
    rfl

end SmcTuring.Native.StringInit

module
public import SmcTuring.Native.StringInitTrace
public import SmcTuring.Native.StringFieldWrites

public section
namespace SmcTuring.Native.StringInitWrites

/-- The present DEFDATA payload derives the indirect x64 stores. x86 has
one four-byte owner store; x64 has four complete native word stores. -/
theorem owned (mode : Mode) (codeStart codeEnd start initial : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : start+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (initialFits : initial+mode.wordBytes<2^(8*mode.wordBytes))
    (fieldInside : codeStart≤StringInit.field mode start ∧ StringInit.field mode start+mode.wordBytes≤codeEnd)
    (initialInside : codeStart≤initial ∧ initial+mode.wordBytes≤codeEnd)
    (current : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=StringInit.bytes mode start initial) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringInit.forms mode start initial).map (StringWrites.liftString mode)) state := by
  have fieldFits : StringInit.field mode start<2^(8*mode.wordBytes) := by
    cases mode <;> simp [StringInit.field,StringCodec.fieldOffset,StringCodec.initialSize,Mode.wordBytes] at fits ⊢ <;> omega
  have pointer:=StringInit.initialized_pointer mode start initial state.principal.memory fits current
  cases mode with
  | x86 =>
    constructor
    · unfold StringWrites.CodeWrite
      change 0<(LittleEndian.wordEncode 4 (BitVec.ofNat 32 initial)).length ∧
        codeStart≤(Arithmetic.encodeNat .x86 (StringInit.field .x86 start)).toNat ∧
        (Arithmetic.encodeNat .x86 (StringInit.field .x86 start)).toNat+(LittleEndian.wordEncode 4 (BitVec.ofNat 32 initial)).length≤codeEnd
      rw [LittleEndian.word_encode_length,Arithmetic.encode_nat_toNat .x86 _ fieldFits]
      exact ⟨by decide,fieldInside⟩
    · trivial
  | x64 =>
    have readerPointer : Execution.load .x64 state.principal.memory (ReaderImage.label .x64 start)=Arithmetic.encodeNat .x64 initial := pointer
    have labelOwned:=StringFieldWrites.word_owned .x64 codeStart codeEnd (StringInit.field .x64 start) fieldFits fieldInside
    have targetOwned:=StringFieldWrites.word_owned .x64 codeStart codeEnd initial
      (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) initialFits) initialInside
    have fields:=Reader.four_writes_owned .x64 state.principal (ReaderImage.label .x64 start)
      (ReaderImage.firstDisp .x64 start) (ReaderImage.secondDisp .x64)
      (ReaderImage.first_hits .x64 start state.principal entry) (ReaderImage.second_hits .x64 start state.principal entry)
      (StringWrites.WordOwned .x64 codeStart codeEnd) labelOwned (by rw [readerPointer];exact targetOwned)
    have actual : Writes.OwnedRun .x64 (StringWrites.WordOwned .x64 codeStart codeEnd)
        [.memory .exchangeAcc (ReaderImage.firstDisp .x64 start),Reader.storeForm .x64 (ReaderImage.label .x64 start) (ReaderImage.secondDisp .x64),
          .exchangeIndirect,.moffs (Arithmetic.encodeNat .x64 initial)] state.principal := by
      rw [←readerPointer]
      simpa only [Writes.OwnedRun,and_true,Reader.swapped,Reader.restored,Reader.dereferenced] using fields
    have lifted:=StringWrites.native_owned_run .x64 codeStart codeEnd _ state actual
    simpa only [StringInit.forms,StringInit.first_displacement,StringInit.second_displacement,
      ReaderImage.firstDisp,ReaderImage.secondDisp,Reader.storeForm,List.map_cons,List.map_nil,StringWrites.liftNative] using lifted

end SmcTuring.Native.StringInitWrites

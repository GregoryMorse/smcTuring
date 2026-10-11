module
public import SmcTuring.Native.StringWrites
public import SmcTuring.Native.StringInitTrace

public section
namespace SmcTuring.Appendix.Listing9DeclarationWrites
open Native

/-- Complete code-word destinations are proved from the present declaration
bytes. The reader's indirect write is its decoded initial pointer, including
the self-pointer case; it is not an ownership premise about a future state. -/
theorem owned (mode : Mode) (codeStart codeEnd owner initial : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode owner)
    (fits : owner+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory owner (StringCodec.initialSize mode)=StringInit.bytes mode owner initial)
    (fieldOwned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode (StringInit.field mode owner)))
    (targetOwned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode initial)) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringInit.forms mode owner initial).map (StringWrites.liftString mode)) state := by
  cases mode with
  | x86 =>
    change StringWrites.CodeWrite .x86 codeStart codeEnd
      (StringWrites.liftString .x86 (.initialize32 (BitVec.ofNat 32 (StringInit.field .x86 owner)) (BitVec.ofNat 32 initial))) state ∧ True
    constructor
    · have size : (StringWrites.packet .x86 (StringWrites.liftString .x86 (.initialize32 (BitVec.ofNat 32 (StringInit.field .x86 owner)) (BitVec.ofNat 32 initial))) state).bytes.length=4 := LittleEndian.word_encode_length _ _
      unfold StringWrites.CodeWrite
      rw [size]
      exact ⟨by decide,fieldOwned⟩
    · trivial
  | x64 =>
    have pointer:=StringInit.initialized_pointer .x64 owner initial state.principal.memory fits current
    change Execution.load .x64 state.principal.memory (ReaderImage.label .x64 owner)=Arithmetic.encodeNat .x64 initial at pointer
    have fields:=Reader.four_writes_owned .x64 state.principal (ReaderImage.label .x64 owner)
      (ReaderImage.firstDisp .x64 owner) (ReaderImage.secondDisp .x64)
      (ReaderImage.first_hits .x64 owner state.principal entry) (ReaderImage.second_hits .x64 owner state.principal entry)
      (StringWrites.WordOwned .x64 codeStart codeEnd) fieldOwned (by rw [pointer];exact targetOwned)
    have actual : Writes.OwnedRun .x64 (StringWrites.WordOwned .x64 codeStart codeEnd)
        [.memory .exchangeAcc (ReaderImage.firstDisp .x64 owner),Reader.storeForm .x64 (ReaderImage.label .x64 owner) (ReaderImage.secondDisp .x64),
          .exchangeIndirect,.moffs (Arithmetic.encodeNat .x64 initial)] state.principal := by
      rw [←pointer]
      simpa only [Writes.OwnedRun,and_true,Reader.swapped,Reader.restored,Reader.dereferenced] using fields
    have lifted:=StringWrites.native_owned_run .x64 codeStart codeEnd _ state actual
    simpa only [StringInit.forms,StringInit.first_displacement,StringInit.second_displacement,ReaderImage.firstDisp,ReaderImage.secondDisp,
      Reader.storeForm,List.map_cons,List.map_nil,StringWrites.liftNative] using lifted

end SmcTuring.Appendix.Listing9DeclarationWrites

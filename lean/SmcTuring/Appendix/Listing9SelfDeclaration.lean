module
public import SmcTuring.Appendix.Listing9SelfReader

public section
namespace SmcTuring.Appendix.Listing9SelfDeclaration
open Native

theorem x64_forms (start : Nat) :
    Listing8CopiedPointer.forms .x64 start start (Arithmetic.encodeNat .x64 (StringInit.field .x64 start))=
      StringInit.forms .x64 start (StringInit.field .x64 start) := by
  simp only [Listing8CopiedPointer.forms,Listing8CopiedPointer.first,Listing8CopiedPointer.second,Listing8CopiedPointer.label,
    Listing8CopiedPointer.origin,Bool.false_eq_true,reduceCtorEq,ite_false,ReaderImage.firstDisp,ReaderImage.secondDisp,
    StringInit.forms,StringInit.first_displacement,StringInit.second_displacement,Reader.storeForm,ReaderImage.label,StringInit.field,
    StringCodec.fieldOffset]

theorem x64_bytes (start : Nat) :
    Listing8Prototypes.pointerBytes .x64 start (Arithmetic.encodeNat .x64 (StringInit.field .x64 start))=
      StringInit.bytes .x64 start (StringInit.field .x64 start) := by
  have encoded:=Listing8CopiedPointer.encoding .x64 start start (Arithmetic.encodeNat .x64 (StringInit.field .x64 start))
  rw [x64_forms,StringInit.forms_encoding] at encoded
  exact encoded.symm

/-- The dynamically rewritten save declaration points to its own full operand
field. Its complete execution is safe and memory preserving in both modes. -/
theorem trace (mode : Mode) (start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : start+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=StringInit.bytes mode start (StringInit.field mode start)) :
    StringExecution.Trace mode state (StringInit.forms mode start (StringInit.field mode start))
      (StringExecution.run mode (StringInit.forms mode start (StringInit.field mode start)) state) := by
  have startFits : start<2^(8*mode.wordBytes) := by omega
  cases mode with
  | x86 =>
    have fetched : StringForm.fetch .x86 state.principal.memory state.principal.pc.toNat=some (.initialize32 (BitVec.ofNat 32 (StringInit.field .x86 start)) (BitVec.ofNat 32 (StringInit.field .x86 start))) := by
      rw [entry,Arithmetic.encode_nat_toNat .x86 _ startFits]
      exact StringForm.fetch_current_encoding .x86 _ _ _ rfl current
    exact .step fetched (.nil _)
  | x64 =>
    have packet : ByteMemory.bytesAt state.principal.memory start (Listing8Prototypes.pointerBytes .x64 start (Arithmetic.encodeNat .x64 (StringInit.field .x64 start))).length=
        Listing8Prototypes.pointerBytes .x64 start (Arithmetic.encodeNat .x64 (StringInit.field .x64 start)) := by
      rw [x64_bytes,StringInit.bytes,StringCodec.initial_length]
      exact current
    have actual:=Listing9SelfReader.trace .x64 start (Arithmetic.encodeNat .x64 (StringInit.field .x64 start)) state entry fits rfl packet
    rw [Listing8CopiedPointer.finish,x64_forms] at actual
    exact actual

theorem effect (mode : Mode) (start : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : start+StringCodec.initialSize mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=StringInit.bytes mode start (StringInit.field mode start)) :
    StringExecution.run mode (StringInit.forms mode start (StringInit.field mode start)) state=
      {state with principal:={state.principal with
        pc:=Arithmetic.encodeNat mode (start+StringCodec.initialSize mode)
        accumulator:=if mode=.x86 then state.principal.accumulator else Arithmetic.encodeNat mode (StringInit.field mode start)}} := by
  have actual:=StringInit.effect mode start (StringInit.field mode start) state entry fits current
  have pointer:=StringInit.initialized_pointer mode start (StringInit.field mode start) state.principal.memory fits current
  rw [actual]
  cases mode with
  | x86 => rfl
  | x64 =>
    change {state with principal:={state.principal with pc:=Arithmetic.encodeNat .x64 (start+27),accumulator:=Execution.load .x64 state.principal.memory (Arithmetic.encodeNat .x64 (StringInit.field .x64 start))}}=_
    rw [pointer]
    rfl

end SmcTuring.Appendix.Listing9SelfDeclaration

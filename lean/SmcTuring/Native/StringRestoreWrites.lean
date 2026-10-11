module
public import SmcTuring.Native.StringFieldWrites
public import SmcTuring.Native.StringRestore

public section
namespace SmcTuring.Native.StringRestoreWrites

/-- Both reached restoration instructions write the same complete cursor
word. Their actual next PCs determine the two displacement addresses. -/
theorem owned (mode : Mode) (destination : Bool) (codeStart codeEnd pc field size : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (exchangeRange : mode=.x64 → Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (subtractRange : mode=.x64 → Relocation.SignedDelta (StringRestore.endpoint mode pc size) field)
    (fieldOwned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode field)) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringRestore.forms mode destination pc field size).map (StringWrites.liftString mode)) state := by
  have first:=StringFieldWrites.exchange mode destination codeStart codeEnd pc field state entry exchangeRange fieldOwned
  have next:=StringFieldWrites.exchange_pc mode destination pc field state entry
  have second:=StringFieldWrites.subtract mode codeStart codeEnd (pc+StringCodec.exchangeSize mode) field size
    (StringExecution.execute mode (StringOperands.exchange mode destination pc field) state) next subtractRange fieldOwned
  exact ⟨first,second,trivial⟩

end SmcTuring.Native.StringRestoreWrites

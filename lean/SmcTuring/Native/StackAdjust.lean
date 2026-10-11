module
public import SmcTuring.Native.StringStack
public import SmcTuring.Native.StringOperands

public section
namespace SmcTuring.Native.StackAdjust
@[expose] def subtract (mode : Mode) (pc field value : Nat) : StringStack.Form mode :=
  .previous (.previous (.string (StringOperands.subtract mode pc field value)))
theorem subtract_encoding (mode : Mode) (pc field value : Nat) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory pc (StringForm.encode mode (StringOperands.subtract mode pc field value)).length =
      StringForm.encode mode (StringOperands.subtract mode pc field value)) :
    StringStack.fetch mode memory pc = some (subtract mode pc field value) := by
  exact StringStack.previous_fetch mode _ _ _ (StringControl.previous_fetch mode _ _ _
    (StringDword.string_fetch mode _ _ _ (StringForm.fetch_current_encoding mode _ _ _ (by unfold StringOperands.subtract;split <;> trivial) current)))
theorem subtract_effect (mode : Mode) (pc field value : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+StringCodec.subSize mode value) field)
    (small : value<2^31) (fits : field<2^(8*mode.wordBytes)) :
    StringStack.execute mode (subtract mode pc field value) state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat mode (pc+StringCodec.subSize mode value)
      carry := Arithmetic.unsignedBorrow (MixedMemory.getWord mode state.principal.memory field) (Arithmetic.encodeNat mode value)
      memory := ByteMemory.putWord mode state.principal.memory field
        (MixedMemory.getWord mode state.principal.memory field-Arithmetic.encodeNat mode value)}} := by
  change StringExecution.execute mode (StringOperands.subtract mode pc field value) state = _
  rw [StringOperands.subtract_effect mode pc field value state entry range small,Execution.storeState,
    MixedMemory.load_nat mode _ _ fits,Arithmetic.encode_nat_toNat mode _ fits]
end SmcTuring.Native.StackAdjust

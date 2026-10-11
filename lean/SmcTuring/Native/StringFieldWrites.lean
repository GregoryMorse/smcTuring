module
public import SmcTuring.Native.StringWrites
public import SmcTuring.Native.StringOperands

public section
namespace SmcTuring.Native.StringFieldWrites

theorem word_owned (mode : Mode) (codeStart codeEnd field : Nat)
    (fits : field<2^(8*mode.wordBytes)) (inside : codeStart≤field ∧ field+mode.wordBytes≤codeEnd) :
    StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode field) := by
  unfold StringWrites.WordOwned
  rw [Arithmetic.encode_nat_toNat mode _ fits]
  exact inside

theorem exchange (mode : Mode) (destination : Bool) (codeStart codeEnd pc field : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (owned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode field)) :
    StringWrites.CodeWrite mode codeStart codeEnd (StringWrites.liftString mode (StringOperands.exchange mode destination pc field)) state := by
  have hits:=StringOperands.exchange_hits mode destination pc field state entry range
  have address : (StringWrites.packet mode (StringWrites.liftString mode (StringOperands.exchange mode destination pc field)) state).address=
      (Arithmetic.encodeNat mode field).toNat := congrArg BitVec.toNat hits
  have size : (StringWrites.packet mode (StringWrites.liftString mode (StringOperands.exchange mode destination pc field)) state).bytes.length=mode.wordBytes := LittleEndian.word_encode_length _ _
  unfold StringWrites.CodeWrite
  rw [address,size]
  exact ⟨by cases mode <;> decide,owned⟩

theorem exchange_pc (mode : Mode) (destination : Bool) (pc field : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc) :
    (StringExecution.execute mode (StringOperands.exchange mode destination pc field) state).principal.pc=
      Arithmetic.encodeNat mode (pc+StringCodec.exchangeSize mode) := by
  cases destination <;> change StringExecution.nextPC mode (StringOperands.exchange mode _ pc field) state=_
  all_goals
    unfold StringExecution.nextPC
    rw [StringOperands.exchange_length,entry]
    exact BitVec.ofNat_add_ofNat _ _

theorem subtract_address (mode : Mode) (pc field size : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+StringCodec.subSize mode size) field) :
    (StringWrites.packet mode (StringWrites.liftString mode (StringOperands.subtract mode pc field size)) state).address=
      (Arithmetic.encodeNat mode field).toNat := by
  have hits : StringExecution.address mode (StringOperands.subtract mode pc field size) state
      (Relocation.memoryDisp mode (pc+StringCodec.subSize mode size) field)=Arithmetic.encodeNat mode field := by
    unfold StringExecution.address
    rw [StringOperands.subtract_next mode pc field size state entry]
    exact Relocation.memory_hits mode _ _ range
  unfold StringOperands.subtract at hits ⊢
  by_cases small : size<128
  · simp only [ite_eq_left small] at hits ⊢
    exact congrArg BitVec.toNat hits
  · simp only [ite_eq_right small] at hits ⊢
    exact congrArg BitVec.toNat hits

theorem subtract_size (mode : Mode) (pc field size : Nat) (state : StringExecution.State mode) :
    (StringWrites.packet mode (StringWrites.liftString mode (StringOperands.subtract mode pc field size)) state).bytes.length=mode.wordBytes := by
  unfold StringOperands.subtract
  split <;> exact LittleEndian.word_encode_length _ _

theorem subtract (mode : Mode) (codeStart codeEnd pc field size : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+StringCodec.subSize mode size) field)
    (owned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode field)) :
    StringWrites.CodeWrite mode codeStart codeEnd (StringWrites.liftString mode (StringOperands.subtract mode pc field size)) state := by
  unfold StringWrites.CodeWrite
  rw [subtract_address mode pc field size state entry range,subtract_size]
  exact ⟨by cases mode <;> decide,owned⟩

end SmcTuring.Native.StringFieldWrites

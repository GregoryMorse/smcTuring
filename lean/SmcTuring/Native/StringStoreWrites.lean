module
public import SmcTuring.Native.StringWrites
public import SmcTuring.Native.DwordRetarget

public section
namespace SmcTuring.Native.StringStoreWrites

@[expose] def liftDword (mode : Mode) (form : StringDword.Form mode) : StringStack.Form mode :=
  .previous (.previous form)

theorem address (mode : Mode) (displacement value : BitVec 32) (state : StringExecution.State mode) :
    (StringWrites.packet mode (liftDword mode (StringDword.store mode displacement value)) state).address=
      (DwordArithmetic.address mode (.store displacement value) state.principal).toNat := by
  cases mode <;> rfl

theorem length (mode : Mode) (displacement value : BitVec 32) (state : StringExecution.State mode) :
    (StringWrites.packet mode (liftDword mode (StringDword.store mode displacement value)) state).bytes.length=4 := by
  cases mode <;> exact LittleEndian.word_encode_length _ _

theorem located (mode : Mode) (codeStart codeEnd pc target : Nat) (value : BitVec 32) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+10) target)
    (fits : target<2^(8*mode.wordBytes)) (inside : codeStart≤target ∧ target+4≤codeEnd) :
    StringWrites.CodeWrite mode codeStart codeEnd
      (liftDword mode (StringDword.store mode (Relocation.memoryDisp mode (pc+10) target) value)) state := by
  have hits:=DwordArithmetic.located_address mode (.store 0 value) pc target state.principal rfl entry range
  change DwordArithmetic.address mode (.store (Relocation.memoryDisp mode (pc+10) target) value) state.principal=
    Arithmetic.encodeNat mode target at hits
  unfold StringWrites.CodeWrite
  rw [address,length,hits,Arithmetic.encode_nat_toNat mode _ fits]
  exact ⟨by decide,inside⟩

theorem next_pc (mode : Mode) (displacement value : BitVec 32) (pc : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc) :
    (StringStack.execute mode (liftDword mode (StringDword.store mode displacement value)) state).principal.pc=
      Arithmetic.encodeNat mode (pc+10) := by
  change (StringDword.execute mode (StringDword.store mode displacement value) state).principal.pc=_
  rw [StringDword.store_execute]
  change state.principal.pc+Arithmetic.encodeNat mode 10=Arithmetic.encodeNat mode (pc+10)
  rw [entry]
  exact BitVec.ofNat_add_ofNat _ _

end SmcTuring.Native.StringStoreWrites

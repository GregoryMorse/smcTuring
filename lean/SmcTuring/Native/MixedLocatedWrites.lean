module
public import SmcTuring.Native.MixedDword

public section
namespace SmcTuring.Native.MixedLocatedWrites

/-- A reached direct DWORD instruction writes its complete four-byte
relocated field, independently of the arithmetic value and flags. -/
theorem field (mode : Mode) (codeStart codeEnd pc target : Nat) (form : DwordArithmetic.Form)
    (state : Execution.State mode) (direct : DwordArithmetic.direct form=true)
    (entry : state.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+DwordArithmetic.length form) target)
    (fits : target<2^(8*mode.wordBytes)) (inside : codeStart≤target ∧ target+4≤codeEnd) :
    codeStart≤(MixedDword.address mode (.arithmetic (DwordArithmetic.located mode form pc target)) state).toNat ∧
      (MixedDword.address mode (.arithmetic (DwordArithmetic.located mode form pc target)) state).toNat+
        MixedDword.width mode (.arithmetic (DwordArithmetic.located mode form pc target))≤codeEnd := by
  change codeStart≤(DwordArithmetic.address mode (DwordArithmetic.located mode form pc target) state).toNat ∧
    (DwordArithmetic.address mode (DwordArithmetic.located mode form pc target) state).toNat+4≤codeEnd
  rw [DwordArithmetic.located_address mode form pc target state direct entry range,Arithmetic.encode_nat_toNat mode _ fits]
  exact inside

end SmcTuring.Native.MixedLocatedWrites

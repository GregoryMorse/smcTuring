module
public import SmcTuring.Native.StringMixed
public import SmcTuring.Native.StringDwordWritesBridge

public section
namespace SmcTuring.Native.StringMixedWrites

theorem address (mode : Mode) (form : MixedDword.Form mode) (state : StringExecution.State mode) :
    (StringWrites.packet mode (StringStoreWrites.liftDword mode (StringMixed.canonical mode form)) state).address=
      (MixedDword.address mode form state.principal).toNat := by
  cases form with
  | arithmetic form => cases mode <;> cases form <;> rfl
  | copy form => cases mode <;> cases form <;> rfl
  | wideExchange d => rfl

theorem length (mode : Mode) (form : MixedDword.Form mode) (state : StringExecution.State mode) :
    (StringWrites.packet mode (StringStoreWrites.liftDword mode (StringMixed.canonical mode form)) state).bytes.length=MixedDword.width mode form := by
  cases form with
  | arithmetic form => cases mode <;> cases form <;> exact LittleEndian.word_encode_length _ _
  | copy form => cases mode <;> cases form <;> exact LittleEndian.word_encode_length _ _
  | wideExchange d => exact LittleEndian.word_encode_length _ _

theorem code_write (mode : Mode) (codeStart codeEnd : Nat) (form : MixedDword.Form mode) (state : StringExecution.State mode)
    (inside : codeStart≤(MixedDword.address mode form state.principal).toNat ∧
      (MixedDword.address mode form state.principal).toNat+MixedDword.width mode form≤codeEnd) :
    StringWrites.CodeWrite mode codeStart codeEnd (StringStoreWrites.liftDword mode (StringMixed.canonical mode form)) state := by
  unfold StringWrites.CodeWrite
  rw [address,length]
  exact ⟨by cases form <;> simp [MixedDword.width],inside⟩

/-- Canonical overlapping x86 forms retain the original store address and
width. The original actual-state ownership lifts through execution. -/
theorem owned_run (mode : Mode) (codeStart codeEnd : Nat) (forms : List (MixedDword.Form mode)) (state : StringExecution.State mode)
    (owned : MixedDword.OwnedRun mode (fun address width => codeStart≤address ∧ address+width≤codeEnd) forms state.principal) :
    StringWrites.OwnedRun mode codeStart codeEnd ((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form forms ih =>
    constructor
    · exact code_write mode codeStart codeEnd form state owned.1
    · change StringWrites.OwnedRun mode codeStart codeEnd ((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode))
        (StringDword.execute mode (StringMixed.canonical mode form) state)
      rw [StringMixed.execute]
      exact ih _ owned.2

end SmcTuring.Native.StringMixedWrites

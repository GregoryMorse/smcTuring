module
public import SmcTuring.Native.StringStackImage

public section
namespace SmcTuring.Native.StringInstructionSizes

theorem string (mode : Mode) (form : StringForm.Form mode) (legal : StringForm.Legal mode form) :
    StringPCSteps.stringSize mode form≤15 := by
  rw [StringStackImage.string_size]
  exact StringForm.length_bound mode form legal

theorem dword (mode : Mode) (form : StringDword.Form mode) (legal : StringStackImage.dwordLegal mode form) :
    StringPCSteps.dwordSize mode form≤15 := by
  cases form with
  | string form => exact string mode form legal
  | mixed form =>
    cases form with
    | arithmetic form => cases form <;> simp [StringPCSteps.dwordSize,MixedDword.length,DwordArithmetic.length]
    | copy form => cases mode <;> cases form <;> simp [StringPCSteps.dwordSize,MixedDword.length,DwordCode.length,Mode.wordBytes]
    | wideExchange => change 7≤15;decide
  | xorAccumulator => change 6≤15;decide

theorem control (mode : Mode) (form : StringControl.Form mode) (legal : StringStackImage.controlLegal mode form) :
    StringPCSteps.controlSize mode form≤15 := by
  cases form with
  | previous form => exact dword mode form legal
  | wideNegation => cases mode <;> simp [StringPCSteps.controlSize,WordNegation.length,wordPrefix]

theorem size (mode : Mode) (form : StringStack.Form mode) (legal : StringStackImage.Legal mode form) :
    StringPCSteps.size mode form≤15 := by
  cases form with
  | previous form => exact control mode form legal
  | addSmall => cases mode <;> simp [StringPCSteps.size,WordAddImmediate.length,wordPrefix]

theorem fetched (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringStack.Form mode)
    (current : StringStack.fetch mode memory pc=some form) : StringPCSteps.size mode form≤15 :=
  size mode form (StringStackImage.fetch mode memory pc form current).2

/-- The actual trace derives its byte-total bound from each positively
decoded instruction; no expected or future packet/size certificate is given. -/
theorem trace_total (mode : Mode) {state finish : StringExecution.State mode} {forms : List (StringStack.Form mode)}
    (actual : StringStack.Trace mode state forms finish) : StringPCSteps.total mode forms≤forms.length*15 := by
  induction actual with
  | nil => simp [StringPCSteps.total]
  | step current rest ih =>
    have bound:=fetched mode _ _ _ current
    simp only [StringPCSteps.total,List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul] at ih ⊢
    omega

end SmcTuring.Native.StringInstructionSizes

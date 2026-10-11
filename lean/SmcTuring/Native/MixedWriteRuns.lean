module
public import SmcTuring.Native.StringMixedWrites

public section
namespace SmcTuring.Native.MixedWriteRuns

@[expose] def run (mode : Mode) : List (MixedDword.Form mode) → Execution.State mode → Execution.State mode
  | [],state => state
  | form::forms,state => run mode forms (MixedDword.execute mode form state)

theorem run_append (mode : Mode) (first second : List (MixedDword.Form mode)) (state : Execution.State mode) :
    run mode (first++second) state=run mode second (run mode first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons form forms ih => exact ih (MixedDword.execute mode form state)

theorem trace_run_eq (mode : Mode) {state final : Execution.State mode} {forms : List (MixedDword.Form mode)}
    (actual : MixedDword.Trace mode state forms final) : run mode forms state=final := by
  induction actual with
  | nil => rfl
  | step current rest ih => exact ih

theorem owned_run_append (mode : Mode) (owned : Nat → Nat → Prop) (first second : List (MixedDword.Form mode)) (state : Execution.State mode) :
    MixedDword.OwnedRun mode owned (first++second) state ↔
      MixedDword.OwnedRun mode owned first state ∧ MixedDword.OwnedRun mode owned second (run mode first state) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append,MixedDword.OwnedRun,run,true_and]
  | cons form forms ih => simp only [List.cons_append,MixedDword.OwnedRun,run,ih,and_assoc]

/-- Canonical native execution retains SI/DI/DF and follows every actual
mixed principal state, including the x86 overlapping decoder forms. -/
theorem canonical_run (mode : Mode) (forms : List (MixedDword.Form mode)) (state : StringExecution.State mode) :
    StringWrites.run mode ((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state=
      {state with principal:=run mode forms state.principal} := by
  induction forms generalizing state with
  | nil => rfl
  | cons form forms ih =>
    change StringWrites.run mode ((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode))
      (StringDword.execute mode (StringMixed.canonical mode form) state)=_
    rw [StringMixed.execute,ih]
    rfl

theorem arithmetic_owned (mode : Mode) (codeStart codeEnd : Nat) (forms : List DwordArithmetic.Form) (state : Execution.State mode)
    (owned : DwordArithmetic.OwnedRun mode (fun address => codeStart≤address ∧ address+4≤codeEnd) forms state) :
    MixedDword.OwnedRun mode (fun address width => codeStart≤address ∧ address+width≤codeEnd) (forms.map MixedDword.Form.arithmetic) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form forms ih => exact ⟨owned.1,ih _ owned.2⟩

theorem copy_owned (mode : Mode) (codeStart codeEnd : Nat) (forms : List (DwordCode.Form mode)) (state : Execution.State mode)
    (owned : DwordCode.OwnedRun mode (fun address => codeStart≤address ∧ address+4≤codeEnd) forms state) :
    MixedDword.OwnedRun mode (fun address width => codeStart≤address ∧ address+width≤codeEnd) (forms.map MixedDword.Form.copy) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form forms ih => exact ⟨owned.1,ih _ owned.2⟩

end SmcTuring.Native.MixedWriteRuns

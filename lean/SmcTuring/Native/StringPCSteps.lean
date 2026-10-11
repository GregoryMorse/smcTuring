module
public import SmcTuring.Native.StringReadRuns

public section
namespace SmcTuring.Native.StringPCSteps

@[expose] def NativeSequential (mode : Mode) : Native.Form mode → Prop
  | .memory .callIndirect _ => False
  | .callRelative d => d=0
  | _ => True
@[expose] def StringSequential (mode : Mode) : StringForm.Form mode → Prop
  | .native form => NativeSequential mode form
  | _ => True
@[expose] def DwordSequential (mode : Mode) : StringDword.Form mode → Prop
  | .string form => StringSequential mode form
  | _ => True
@[expose] def ControlSequential (mode : Mode) : StringControl.Form mode → Prop
  | .previous form => DwordSequential mode form
  | _ => True
@[expose] def Sequential (mode : Mode) : StringStack.Form mode → Prop
  | .previous form => ControlSequential mode form
  | _ => True

@[expose] def stringSize (mode : Mode) : StringForm.Form mode → Nat
  | .native form => Native.instructionLength mode form
  | form => StringForm.length mode form
@[expose] def dwordSize (mode : Mode) : StringDword.Form mode → Nat
  | .string form => stringSize mode form
  | .mixed form => MixedDword.length mode form
  | .xorAccumulator _ => 6
@[expose] def controlSize (mode : Mode) : StringControl.Form mode → Nat
  | .previous form => dwordSize mode form
  | .wideNegation _ => WordNegation.length mode
@[expose] def size (mode : Mode) : StringStack.Form mode → Nat
  | .previous form => controlSize mode form
  | .addSmall _ _ => WordAddImmediate.length mode

theorem native_pc (mode : Mode) (form : Native.Form mode) (state : Execution.State mode)
    (sequential : NativeSequential mode form) :
    (Execution.execute mode form state).pc=state.pc+Arithmetic.encodeNat mode (Native.instructionLength mode form) := by
  cases form with
  | moffs => rfl
  | exchangeIndirect => rfl
  | memory operation d =>
    cases operation <;> first | exact False.elim sequential | rfl
  | callRelative d =>
    change d=0 at sequential
    subst d
    cases mode <;> simp only [Execution.execute,Execution.callState,Execution.nextPC,Execution.displacementWord]
    all_goals exact BitVec.add_zero _

theorem string_pc (mode : Mode) (form : StringForm.Form mode) (state : StringExecution.State mode)
    (sequential : StringSequential mode form) :
    (StringExecution.execute mode form state).principal.pc=state.principal.pc+Arithmetic.encodeNat mode (stringSize mode form) := by
  cases form with
  | native form => exact native_pc mode form state.principal sequential
  | initialize32 => rfl
  | exchangeIndex destination => cases destination <;> rfl
  | subtractSmall => rfl
  | subtractFull => rfl
  | move => rfl

theorem arithmetic_pc (mode : Mode) (form : DwordArithmetic.Form) (state : Execution.State mode) :
    (DwordArithmetic.execute mode form state).pc=state.pc+Arithmetic.encodeNat mode (DwordArithmetic.length form) := rfl

theorem copy_pc (mode : Mode) (form : DwordCode.Form mode) (state : Execution.State mode) :
    (DwordCode.execute mode form state).pc=state.pc+Arithmetic.encodeNat mode (DwordCode.length mode form) := by
  cases form <;> rfl

theorem mixed_pc (mode : Mode) (form : MixedDword.Form mode) (state : Execution.State mode) :
    (MixedDword.execute mode form state).pc=state.pc+Arithmetic.encodeNat mode (MixedDword.length mode form) := by
  cases form with
  | arithmetic form => exact arithmetic_pc mode form state
  | copy form => exact copy_pc mode form state
  | wideExchange => rfl

theorem dword_pc (mode : Mode) (form : StringDword.Form mode) (state : StringExecution.State mode)
    (sequential : DwordSequential mode form) :
    (StringDword.execute mode form state).principal.pc=state.principal.pc+Arithmetic.encodeNat mode (dwordSize mode form) := by
  cases form with
  | string form => exact string_pc mode form state sequential
  | mixed form => exact mixed_pc mode form state.principal
  | xorAccumulator => rfl

theorem control_pc (mode : Mode) (form : StringControl.Form mode) (state : StringExecution.State mode)
    (sequential : ControlSequential mode form) :
    (StringControl.execute mode form state).principal.pc=state.principal.pc+Arithmetic.encodeNat mode (controlSize mode form) := by
  cases form with
  | previous form => exact dword_pc mode form state sequential
  | wideNegation => rfl

theorem step_pc (mode : Mode) (form : StringStack.Form mode) (state : StringExecution.State mode)
    (sequential : Sequential mode form) :
    (StringStack.execute mode form state).principal.pc=state.principal.pc+Arithmetic.encodeNat mode (size mode form) := by
  cases form with
  | previous form => exact control_pc mode form state sequential
  | addSmall => rfl

theorem located_pc (mode : Mode) (form : StringStack.Form mode) (state : StringExecution.State mode) (pc : Nat)
    (sequential : Sequential mode form) (entry : state.principal.pc=Arithmetic.encodeNat mode pc) :
    (StringStack.execute mode form state).principal.pc=Arithmetic.encodeNat mode (pc+size mode form) := by
  rw [step_pc mode form state sequential,entry]
  exact BitVec.ofNat_add_ofNat _ _

@[expose] def total (mode : Mode) (forms : List (StringStack.Form mode)) := (forms.map (size mode)).sum

theorem total_append (mode : Mode) (first second : List (StringStack.Form mode)) :
    total mode (first++second)=total mode first+total mode second := by simp [total]

/-- PC advances follow the actual modeled effects and static forms. Memory,
register and flag values are unrestricted; no later PC is a premise. -/
theorem run_pc (mode : Mode) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (sequential : ∀ form∈forms,Sequential mode form) :
    (StringWrites.run mode forms state).principal.pc=state.principal.pc+Arithmetic.encodeNat mode (total mode forms) := by
  induction forms generalizing state with
  | nil => simp [StringWrites.run,total,Arithmetic.encodeNat]
  | cons form rest ih =>
    rw [StringWrites.run,ih _ (fun later member => sequential later (List.Mem.tail _ member)),step_pc mode form state (sequential form (List.Mem.head _))]
    simp only [total,List.map_cons,List.sum_cons]
    rw [BitVec.add_assoc]
    exact congrArg (fun value => state.principal.pc+value) (BitVec.ofNat_add_ofNat _ _)

end SmcTuring.Native.StringPCSteps

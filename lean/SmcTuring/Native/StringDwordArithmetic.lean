module
public import SmcTuring.Native.StringDwordCopy

public section
namespace SmcTuring.Native.StringDwordArithmetic

@[expose] def canonical (mode : Mode) (form : DwordArithmetic.Form) : StringDword.Form mode :=
  match mode,form with
  | .x86,.store d v => StringDword.store .x86 d v
  | .x86,.subtract d v => .string (.subtractFull d v)
  | .x86,.sbbZero d => StringDwordCopy.native .x86 (.memory .subtractBorrowZero d)
  | _,form => .mixed (.arithmetic form)

theorem fallback (mode : Mode) (form : DwordArithmetic.Form) (memory : ByteMemory.Memory) (pc : Nat)
    (current : ByteMemory.bytesAt memory pc (DwordArithmetic.encode form).length = DwordArithmetic.encode form)
    (noLength : StringForm.lengthOfBytes mode ((DwordArithmetic.encode form).take 3) = none) :
    StringDword.fetch mode memory pc = some (.mixed (.arithmetic form)) := by
  have bound : 3 ≤ (DwordArithmetic.encode form).length := by
    cases form <;> simp [DwordArithmetic.encode_length,DwordArithmetic.length]
  have noString : StringForm.fetch mode memory pc = none := by
    rw [StringForm.fetch,←Fetch.bytes_at_take memory pc _ 3 bound,current,noLength];rfl
  rw [StringDword.fetch,noString,MixedDword.arithmetic_encoding mode memory pc form current] <;> rfl

theorem encoding (mode : Mode) (form : DwordArithmetic.Form) (memory : ByteMemory.Memory) (pc : Nat)
    (current : ByteMemory.bytesAt memory pc (DwordArithmetic.encode form).length = DwordArithmetic.encode form) :
    StringDword.fetch mode memory pc = some (canonical mode form) := by
  cases mode with
  | x86 =>
    cases form with
    | store d v => exact StringDword.store_encoding .x86 memory pc d v current
    | subtract d v =>
      exact StringDword.string_fetch .x86 memory pc (.subtractFull d v)
        (StringForm.fetch_current_encoding .x86 memory pc (.subtractFull d v) (by trivial) current)
    | sbbZero d => exact StringDwordCopy.native_encoding .x86 (.memory .subtractBorrowZero d) memory pc current
    | bitXor d v => exact fallback .x86 (.bitXor d v) memory pc current (by rfl)
    | bitAnd d v => exact fallback .x86 (.bitAnd d v) memory pc current (by rfl)
    | bitOr d v => exact fallback .x86 (.bitOr d v) memory pc current (by rfl)
    | negate d => exact fallback .x86 (.negate d) memory pc current (by rfl)
    | complement d => exact fallback .x86 (.complement d) memory pc current (by rfl)
    | xorAtAccumulator v => exact fallback .x86 (.xorAtAccumulator v) memory pc current (by rfl)
  | x64 => cases form <;> exact fallback .x64 _ memory pc current (by rfl)

/-- The selected canonical x86 overlap has the same DWORD effect on all
memory/register/CF inputs; long mode keeps the bare DWORD decoder. -/
theorem execute (mode : Mode) (form : DwordArithmetic.Form) (state : StringExecution.State mode) :
    StringDword.execute mode (canonical mode form) state =
      {state with principal := DwordArithmetic.execute mode form state.principal} := by
  cases mode with
  | x86 =>
    cases form with
    | store d v => exact StringDword.store_execute .x86 d v state
    | subtract d v =>
      simp [canonical,StringDword.execute,StringExecution.execute,StringExecution.address,StringExecution.nextPC,
        StringForm.length,StringForm.encode,wordPrefix,DwordArithmetic.execute,DwordArithmetic.next,
        DwordArithmetic.address,DwordArithmetic.value,DwordArithmetic.carry,DwordArithmetic.flag,
        DwordArithmetic.result,DwordArithmetic.prior,DwordArithmetic.length,Execution.memoryAddress,
        Execution.load,Execution.displacementWord,Execution.storeState,Arithmetic.unsignedBorrow,
        DwordCode.get,DwordCode.put,ByteMemory.putWord,Mode.wordBytes] <;> rfl
    | sbbZero d =>
      simp [canonical,StringDwordCopy.native,StringDword.execute,StringExecution.execute,Execution.execute,
        Execution.executeMemory,Execution.nextPC,Execution.memoryAddress,Execution.load,Execution.storeState,
        Native.instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,
        DwordArithmetic.execute,DwordArithmetic.next,DwordArithmetic.address,DwordArithmetic.value,
        DwordArithmetic.carry,DwordArithmetic.flag,DwordArithmetic.result,DwordArithmetic.prior,
        DwordArithmetic.length,DwordCode.get,DwordCode.put,ByteMemory.putWord,Mode.wordBytes] <;> rfl
    | bitXor d v => rfl
    | bitAnd d v => rfl
    | bitOr d v => rfl
    | negate d => rfl
    | complement d => rfl
    | xorAtAccumulator v => rfl
  | x64 => cases form <;> rfl

end SmcTuring.Native.StringDwordArithmetic

module
public import SmcTuring.Native.StringExecution
public import SmcTuring.Native.MixedDword
public import SmcTuring.Native.DwordXor

public section
namespace SmcTuring.Native.StringDword

/-- One current-byte decoder and state for literal string-copy, full-width
native and bare DWORD instructions. String forms take precedence where the
x86 encodings coincide; the explicit store bridge proves equal effects. -/
inductive Form (mode : Mode) where
  | string (form : StringForm.Form mode)
  | mixed (form : MixedDword.Form mode)
  | xorAccumulator (displacement : BitVec 32)
  deriving DecidableEq
@[expose] def fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : Option (Form mode) :=
  match StringForm.fetch mode memory pc with
  | some form => some (.string form)
  | none => match MixedDword.fetch mode memory pc with
    | some form => some (.mixed form)
    | none => (DwordXor.fetch mode memory pc).map Form.xorAccumulator
@[expose] def execute (mode : Mode) (form : Form mode) (state : StringExecution.State mode) : StringExecution.State mode :=
  match form with
  | .string form => StringExecution.execute mode form state
  | .mixed form => { state with principal := MixedDword.execute mode form state.principal }
  | .xorAccumulator displacement => { state with principal := DwordXor.execute mode displacement state.principal }
@[expose] def step (mode : Mode) (state : StringExecution.State mode) :=
  (fetch mode state.principal.memory state.principal.pc.toNat).map (fun form => execute mode form state)
inductive Trace (mode : Mode) : StringExecution.State mode → List (Form mode) → StringExecution.State mode → Prop
  | nil (state) : Trace mode state [] state
  | step {state final forms form} (current : fetch mode state.principal.memory state.principal.pc.toNat = some form)
      (rest : Trace mode (execute mode form state) forms final) : Trace mode state (form::forms) final

theorem string_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringForm.Form mode)
    (current : StringForm.fetch mode memory pc = some form) : fetch mode memory pc = some (.string form) := by
  rw [fetch,current]
theorem string_trace (mode : Mode) {state final : StringExecution.State mode} {forms : List (StringForm.Form mode)}
    (trace : StringExecution.Trace mode state forms final) : Trace mode state (forms.map Form.string) final := by
  induction trace with
  | nil => exact .nil _
  | step current rest ih => exact .step (string_fetch mode _ _ _ current) ih
theorem trace_append (mode : Mode) {state middle final : StringExecution.State mode} {first second : List (Form mode)}
    (a : Trace mode state first middle) (b : Trace mode middle second final) : Trace mode state (first++second) final := by
  induction a with
  | nil => exact b
  | step current rest ih => exact .step current (ih b)

@[expose] def store (mode : Mode) (displacement value : BitVec 32) : Form mode :=
  match mode with
  | .x86 => .string (.initialize32 displacement value)
  | .x64 => .mixed (.arithmetic (.store displacement value))

theorem store_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (d v : BitVec 32)
    (current : ByteMemory.bytesAt memory pc 10 = DwordArithmetic.encode (.store d v)) :
    fetch mode memory pc = some (store mode d v) := by
  cases mode with
  | x86 =>
    exact string_fetch .x86 memory pc (.initialize32 d v)
      (StringForm.fetch_current_encoding .x86 memory pc (.initialize32 d v) rfl current)
  | x64 =>
    have noLength : StringForm.lengthOfBytes .x64 (ByteMemory.bytesAt memory pc 3) = none := by
      rw [←Fetch.bytes_at_take memory pc 10 3 (by decide),current]
      rfl
    have noString : StringForm.fetch .x64 memory pc = none := by
      rw [StringForm.fetch,noLength]
      rfl
    rw [fetch,noString,MixedDword.arithmetic_encoding .x64 memory pc (.store d v) current]
    rfl

theorem store_execute (mode : Mode) (d v : BitVec 32) (state : StringExecution.State mode) :
    execute mode (store mode d v) state = { state with principal := DwordArithmetic.execute mode (.store d v) state.principal } := by
  cases mode <;> rfl

theorem store_trace (mode : Mode) (d v : BitVec 32) (state : StringExecution.State mode)
    (current : ByteMemory.bytesAt state.principal.memory state.principal.pc.toNat 10 = DwordArithmetic.encode (.store d v)) :
    Trace mode state [store mode d v] { state with principal := DwordArithmetic.execute mode (.store d v) state.principal } := by
  rw [←store_execute]
  exact .step (store_encoding mode _ _ d v current) (.nil _)

end SmcTuring.Native.StringDword

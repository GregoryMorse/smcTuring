module
public import SmcTuring.Native.WordNegation
public import SmcTuring.Native.StringDwordArithmetic

public section
namespace SmcTuring.Native.StringControl
/-- Conservative current-byte extension of the audited string/DWORD decoder.
The additional selected form is full-width NEG, including REX.W in long mode. -/
inductive Form (mode : Mode) where
  | previous (form : StringDword.Form mode)
  | wideNegation (d : BitVec 32)
  deriving DecidableEq
@[expose] def fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : Option (Form mode) :=
  match StringDword.fetch mode memory pc with
  | some form => some (.previous form)
  | none => (WordNegation.fetch mode memory pc).map Form.wideNegation
@[expose] def execute (mode : Mode) (form : Form mode) (state : StringExecution.State mode) :=
  match form with
  | .previous form => StringDword.execute mode form state
  | .wideNegation d => {state with principal := WordNegation.execute mode d state.principal}
inductive Trace (mode : Mode) : StringExecution.State mode → List (Form mode) → StringExecution.State mode → Prop
  | nil (state) : Trace mode state [] state
  | step {state final forms form} (current : fetch mode state.principal.memory state.principal.pc.toNat = some form)
      (rest : Trace mode (execute mode form state) forms final) : Trace mode state (form::forms) final

theorem previous_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringDword.Form mode)
    (current : StringDword.fetch mode memory pc = some form) :
    fetch mode memory pc = some (.previous form) := by rw [fetch,current]

theorem previous_trace (mode : Mode) {state final : StringExecution.State mode} {forms : List (StringDword.Form mode)}
    (actual : StringDword.Trace mode state forms final) : Trace mode state (forms.map Form.previous) final := by
  induction actual with
  | nil => exact .nil _
  | step current rest ih => exact .step (previous_fetch mode _ _ _ current) ih

theorem trace_append (mode : Mode) {state middle final : StringExecution.State mode} {first second : List (Form mode)}
    (a : Trace mode state first middle) (b : Trace mode middle second final) : Trace mode state (first++second) final := by
  induction a with
  | nil => exact b
  | step current rest ih => exact .step current (ih b)

@[expose] def negation (mode : Mode) (d : BitVec 32) : Form mode :=
  match mode with
  | .x86 => .previous (StringDwordArithmetic.canonical .x86 (.negate d))
  | .x64 => .wideNegation d

theorem wide_previous_none (memory : ByteMemory.Memory) (pc : Nat) (d : BitVec 32)
    (current : ByteMemory.bytesAt memory pc 7 = WordNegation.encode .x64 d) :
    StringDword.fetch .x64 memory pc = none := by
  have head : ByteMemory.bytesAt memory pc 3 = [0x48,0xf7,0x1d] := by
    rw [←Fetch.bytes_at_take memory pc 7 3 (by decide),current];rfl
  have two : ByteMemory.bytesAt memory pc 2 = [0x48,0xf7] := by
    rw [←Fetch.bytes_at_take memory pc 3 2 (by decide),head];rfl
  have first : memory pc = 0x48 := by
    have h := congrArg (fun bytes : List LittleEndian.Byte => bytes[0]?) head
    change some (memory pc) = some (0x48 : LittleEndian.Byte) at h
    exact Option.some.inj h
  have noString : StringForm.fetch .x64 memory pc = none := by rw [StringForm.fetch,head];rfl
  have noNative : Fetch.fetch .x64 memory pc = none := by rw [Fetch.fetch,head];rfl
  have noMixed : MixedDword.fetch .x64 memory pc = none := by
    rw [MixedDword.fetch,two];simp only [DwordArithmetic.packetSize,first,ite_true,noNative,Option.bind_none]
    rfl
  have noXor : DwordXor.fetch .x64 memory pc = none := by
    rw [DwordXor.fetch,show 6=3+3 from rfl,ByteWindow.append,head];rfl
  rw [StringDword.fetch,noString,noMixed,noXor];rfl

theorem negation_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (d : BitVec 32)
    (current : ByteMemory.bytesAt memory pc (WordNegation.encode mode d).length = WordNegation.encode mode d) :
    fetch mode memory pc = some (negation mode d) := by
  cases mode with
  | x86 => exact previous_fetch .x86 memory pc _ (StringDwordArithmetic.encoding .x86 (.negate d) memory pc current)
  | x64 => rw [fetch,wide_previous_none memory pc d current,WordNegation.fetch_encoding .x64 memory pc d current];rfl

theorem negation_execute (mode : Mode) (d : BitVec 32) (state : StringExecution.State mode) :
    execute mode (negation mode d) state = {state with principal := WordNegation.execute mode d state.principal} := by
  cases mode with
  | x86 =>
    rw [negation,execute,StringDwordArithmetic.execute]
    rfl
  | x64 => rfl

end SmcTuring.Native.StringControl

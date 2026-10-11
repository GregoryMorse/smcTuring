module
public import SmcTuring.Native.StringControl
public import SmcTuring.Native.WordAddImmediate
public import SmcTuring.Native.StringDwordCopy

public section
namespace SmcTuring.Native.StringStack
/-- Conservative current-byte decoder including the printed stack ADD. -/
inductive Form (mode : Mode) where
  | previous (form : StringControl.Form mode)
  | addSmall (d : BitVec 32) (value : LittleEndian.Byte)
  deriving DecidableEq
@[expose] def fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) : Option (Form mode) :=
  match StringControl.fetch mode memory pc with
  | some form => some (.previous form)
  | none => (WordAddImmediate.fetch mode memory pc).map fun pair => .addSmall pair.1 pair.2
@[expose] def execute (mode : Mode) (form : Form mode) (state : StringExecution.State mode) :=
  match form with
  | .previous form => StringControl.execute mode form state
  | .addSmall d value => {state with principal := WordAddImmediate.execute mode d value state.principal}
inductive Trace (mode : Mode) : StringExecution.State mode → List (Form mode) → StringExecution.State mode → Prop
  | nil (state) : Trace mode state [] state
  | step {state final forms form} (current : fetch mode state.principal.memory state.principal.pc.toNat = some form)
      (rest : Trace mode (execute mode form state) forms final) : Trace mode state (form::forms) final

theorem previous_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringControl.Form mode)
    (current : StringControl.fetch mode memory pc = some form) : fetch mode memory pc = some (.previous form) := by rw [fetch,current]
theorem previous_trace (mode : Mode) {state final : StringExecution.State mode} {forms : List (StringControl.Form mode)}
    (actual : StringControl.Trace mode state forms final) : Trace mode state (forms.map Form.previous) final := by
  induction actual with
  | nil => exact .nil _
  | step current rest ih => exact .step (previous_fetch mode _ _ _ current) ih
theorem trace_append (mode : Mode) {state middle final : StringExecution.State mode} {first second : List (Form mode)}
    (a : Trace mode state first middle) (b : Trace mode middle second final) : Trace mode state (first++second) final := by
  induction a with
  | nil => exact b
  | step current rest ih => exact .step current (ih b)

theorem add_previous_none (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (d : BitVec 32) (value : LittleEndian.Byte)
    (current : ByteMemory.bytesAt memory pc (WordAddImmediate.encode mode d value).length = WordAddImmediate.encode mode d value) :
    StringControl.fetch mode memory pc = none := by
  have head : ByteMemory.bytesAt memory pc 3 = (WordAddImmediate.encode mode d value).take 3 := by
    rw [←Fetch.bytes_at_take memory pc (WordAddImmediate.encode mode d value).length 3
      (by rw [WordAddImmediate.encode_length];cases mode <;> decide),current]
  have two : ByteMemory.bytesAt memory pc 2 = (WordAddImmediate.encode mode d value).take 2 := by
    rw [←Fetch.bytes_at_take memory pc 3 2 (by decide),head,List.take_take];rfl
  have noString : StringForm.fetch mode memory pc = none := by
    rw [StringForm.fetch,head];cases mode <;> rfl
  have noNative : Fetch.fetch mode memory pc = none := by
    rw [Fetch.fetch,head];cases mode <;> rfl
  have noMixed : MixedDword.fetch mode memory pc = none := by
    have first := congrArg (fun bytes : List LittleEndian.Byte => bytes[0]?) head
    cases mode with
    | x86 =>
      have initial : memory pc = 0x83 := by
        change some (memory pc) = some (0x83 : LittleEndian.Byte) at first
        exact Option.some.inj first
      have noCopy : DwordCode.fetch .x86 memory pc = none := by
        rw [DwordCode.fetch,DwordCode.packetSize,initial]
        simp only [show (0x83 : LittleEndian.Byte) ≠ 0xa3 by decide,ite_false]
        rw [show 6=2+4 from rfl,ByteWindow.append,two];rfl
      rw [MixedDword.fetch,two,show DwordArithmetic.packetSize ((WordAddImmediate.encode .x86 d value).take 2)=none from rfl,noCopy]
      rfl
    | x64 =>
      have initial : memory pc = 0x48 := by
        change some (memory pc) = some (0x48 : LittleEndian.Byte) at first
        exact Option.some.inj first
      rw [MixedDword.fetch,two];simp only [WordAddImmediate.encode,wordPrefix,initial,ite_true,noNative,Option.bind_none]
      rfl
  have noXor : DwordXor.fetch mode memory pc = none := by
    rw [DwordXor.fetch,show 6=3+3 from rfl,ByteWindow.append,head];cases mode <;> rfl
  have noNeg : WordNegation.fetch mode memory pc = none := by
    have small : 3 ≤ WordNegation.length mode := by cases mode <;> decide
    have kept := Fetch.bytes_at_take memory pc (WordNegation.length mode) 3 small
    have window : ByteMemory.bytesAt memory pc (WordNegation.length mode) =
        ByteMemory.bytesAt memory pc 3 ++ (ByteMemory.bytesAt memory pc (WordNegation.length mode)).drop 3 := by
      rw [←kept,List.take_append_drop]
    rw [WordNegation.fetch,window,head];cases mode <;> rfl
  rw [StringControl.fetch,StringDword.fetch,noString,noMixed,noXor,noNeg];rfl

theorem add_encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (d : BitVec 32) (value : LittleEndian.Byte)
    (current : ByteMemory.bytesAt memory pc (WordAddImmediate.encode mode d value).length = WordAddImmediate.encode mode d value) :
    fetch mode memory pc = some (.addSmall d value) := by
  rw [fetch,add_previous_none mode memory pc d value current,WordAddImmediate.fetch_encoding mode memory pc d value current];rfl

@[expose] def native (mode : Mode) (form : Native.Form mode) : Form mode :=
  .previous (.previous (StringDwordCopy.native mode form))
theorem native_encoding (mode : Mode) (form : Native.Form mode) (memory : ByteMemory.Memory) (pc : Nat)
    (current : ByteMemory.bytesAt memory pc (Native.encode mode form).length = Native.encode mode form) :
    fetch mode memory pc = some (native mode form) :=
  previous_fetch mode _ _ _ (StringControl.previous_fetch mode _ _ _ (StringDwordCopy.native_encoding mode form _ _ current))
theorem native_execute (mode : Mode) (form : Native.Form mode) (state : StringExecution.State mode) :
    execute mode (native mode form) state = {state with principal := Execution.execute mode form state.principal} := rfl
end SmcTuring.Native.StringStack

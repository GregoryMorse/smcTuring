module
public import SmcTuring.Native.StringStack

public section
namespace SmcTuring.Native.StringWrites
open LittleEndian

/-- The actual memory store, including an unchanged-value store. -/
structure Packet where
  address : Nat
  bytes : List Byte

@[expose] def native (mode : Mode) (form : Native.Form mode) (state : Execution.State mode) : Packet :=
  ⟨(Writes.address mode form state).toNat,wordEncode mode.wordBytes (Writes.value mode form state)⟩
@[expose] def string (mode : Mode) (form : StringForm.Form mode) (state : StringExecution.State mode) : Packet :=
  match form with
  | .native form => native mode form state.principal
  | .initialize32 address value => ⟨address.toNat,wordEncode 4 value⟩
  | .exchangeIndex destination d =>
      ⟨(StringExecution.address mode form state d).toNat,
        wordEncode mode.wordBytes (if destination then state.destinationIndex else state.sourceIndex)⟩
  | .subtractSmall d value =>
      let address:=StringExecution.address mode form state d
      ⟨address.toNat,wordEncode mode.wordBytes (Execution.load mode state.principal.memory address-value.signExtend (8*mode.wordBytes))⟩
  | .subtractFull d value =>
      let address:=StringExecution.address mode form state d
      ⟨address.toNat,wordEncode mode.wordBytes (Execution.load mode state.principal.memory address-Execution.displacementWord mode value)⟩
  | .move width => ⟨state.destinationIndex.toNat,ByteMemory.bytesAt state.principal.memory state.sourceIndex.toNat width⟩
@[expose] def mixed (mode : Mode) (form : MixedDword.Form mode) (state : Execution.State mode) : Packet :=
  match form with
  | .arithmetic form => ⟨(DwordArithmetic.address mode form state).toNat,wordEncode 4 (DwordArithmetic.value mode form state)⟩
  | .copy form => ⟨(DwordCode.address mode form state).toNat,wordEncode 4 (DwordCode.low mode state.accumulator)⟩
  | .wideExchange d => native .x64 (.memory .exchangeAcc d) state
@[expose] def dword (mode : Mode) (form : StringDword.Form mode) (state : StringExecution.State mode) : Packet :=
  match form with
  | .string form => string mode form state
  | .mixed form => mixed mode form state.principal
  | .xorAccumulator d => ⟨(DwordXor.address mode d state.principal).toNat,
      wordEncode 4 (DwordCode.get state.principal.memory (DwordXor.address mode d state.principal).toNat ^^^ DwordCode.low mode state.principal.accumulator)⟩
@[expose] def control (mode : Mode) (form : StringControl.Form mode) (state : StringExecution.State mode) : Packet :=
  match form with
  | .previous form => dword mode form state
  | .wideNegation d =>
      let address:=WordNegation.address mode d state.principal
      ⟨address.toNat,wordEncode mode.wordBytes (-Execution.load mode state.principal.memory address)⟩
@[expose] def packet (mode : Mode) (form : StringStack.Form mode) (state : StringExecution.State mode) : Packet :=
  match form with
  | .previous form => control mode form state
  | .addSmall d value =>
      let address:=WordAddImmediate.address mode d state.principal
      ⟨address.toNat,wordEncode mode.wordBytes (Execution.load mode state.principal.memory address+WordAddImmediate.immediate mode value)⟩

theorem string_memory (mode : Mode) (form : StringForm.Form mode) (state : StringExecution.State mode) :
    (StringExecution.execute mode form state).principal.memory=
      ByteMemory.putBytes state.principal.memory (string mode form state).address (string mode form state).bytes := by
  cases form with
  | native form => exact Writes.execute_memory mode form state.principal
  | initialize32 address value => rfl
  | exchangeIndex destination d => cases destination <;> rfl
  | subtractSmall d value => rfl
  | subtractFull d value => rfl
  | move width => rfl

theorem mixed_memory (mode : Mode) (form : MixedDword.Form mode) (state : Execution.State mode) :
    (MixedDword.execute mode form state).memory=
      ByteMemory.putBytes state.memory (mixed mode form state).address (mixed mode form state).bytes := by
  cases form with
  | arithmetic form => rfl
  | copy form => cases form <;> rfl
  | wideExchange d => exact Writes.execute_memory .x64 (.memory .exchangeAcc d) state

theorem dword_memory (mode : Mode) (form : StringDword.Form mode) (state : StringExecution.State mode) :
    (StringDword.execute mode form state).principal.memory=
      ByteMemory.putBytes state.principal.memory (dword mode form state).address (dword mode form state).bytes := by
  cases form with
  | string form => exact string_memory mode form state
  | mixed form => exact mixed_memory mode form state.principal
  | xorAccumulator d => rfl

theorem control_memory (mode : Mode) (form : StringControl.Form mode) (state : StringExecution.State mode) :
    (StringControl.execute mode form state).principal.memory=
      ByteMemory.putBytes state.principal.memory (control mode form state).address (control mode form state).bytes := by
  cases form with
  | previous form => exact dword_memory mode form state
  | wideNegation d => rfl

theorem execute_memory (mode : Mode) (form : StringStack.Form mode) (state : StringExecution.State mode) :
    (StringStack.execute mode form state).principal.memory=
      ByteMemory.putBytes state.principal.memory (packet mode form state).address (packet mode form state).bytes := by
  cases form with
  | previous form => exact control_memory mode form state
  | addSmall d value => rfl

/-- All bytes of a nonempty architectural write lie in this emitted code
interval. This counts writes whose values already equal the current bytes. -/
@[expose] def CodeWrite (mode : Mode) (start stop : Nat) (form : StringStack.Form mode) (state : StringExecution.State mode) : Prop :=
  0<(packet mode form state).bytes.length ∧ start≤(packet mode form state).address ∧
    (packet mode form state).address+(packet mode form state).bytes.length≤stop
@[expose] def OwnedRun (mode : Mode) (start stop : Nat) : List (StringStack.Form mode) → StringExecution.State mode → Prop
  | [],_ => True
  | form::rest,state => CodeWrite mode start stop form state ∧ OwnedRun mode start stop rest (StringStack.execute mode form state)
@[expose] def run (mode : Mode) : List (StringStack.Form mode) → StringExecution.State mode → StringExecution.State mode
  | [],state => state
  | form::rest,state => run mode rest (StringStack.execute mode form state)
@[expose] def liftString (mode : Mode) (form : StringForm.Form mode) : StringStack.Form mode :=
  .previous (.previous (.string form))
@[expose] def liftNative (mode : Mode) (form : Native.Form mode) : StringStack.Form mode := liftString mode (.native form)
@[expose] def WordOwned (mode : Mode) (start stop : Nat) (address : Word mode) : Prop :=
  start≤address.toNat ∧ address.toNat+mode.wordBytes≤stop

theorem code_write_nonempty (mode : Mode) (start stop : Nat) (form : StringStack.Form mode) (state : StringExecution.State mode)
    (owned : CodeWrite mode start stop form state) : (packet mode form state).bytes≠[] := by
  intro empty
  have positive:=owned.1
  rw [empty] at positive
  exact Nat.lt_irrefl 0 positive

theorem code_write_bytes (mode : Mode) (start stop : Nat) (form : StringStack.Form mode) (state : StringExecution.State mode)
    (owned : CodeWrite mode start stop form state) (position : Nat)
    (inside : ByteMemory.Inside (packet mode form state).address (packet mode form state).bytes.length position) :
    start≤position ∧ position<stop := by unfold ByteMemory.Inside at inside;rcases owned with ⟨_,lower,upper⟩;omega

theorem execute_frame (mode : Mode) (start stop : Nat) (form : StringStack.Form mode) (state : StringExecution.State mode)
    (owned : CodeWrite mode start stop form state) (position : Nat) (outside : position<start ∨ stop≤position) :
    (StringStack.execute mode form state).principal.memory position=state.principal.memory position := by
  rw [execute_memory];apply ByteMemory.put_frame
  intro inside
  have included:=code_write_bytes mode start stop form state owned position inside
  rcases outside with before | after <;> omega

theorem run_append (mode : Mode) (first second : List (StringStack.Form mode)) (state : StringExecution.State mode) :
    run mode (first++second) state=run mode second (run mode first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons form rest ih => exact ih (StringStack.execute mode form state)

theorem run_lift_string (mode : Mode) (forms : List (StringForm.Form mode)) (state : StringExecution.State mode) :
    run mode (forms.map (liftString mode)) state=StringExecution.run mode forms state := by
  induction forms generalizing state with
  | nil => rfl
  | cons form rest ih => exact ih (StringExecution.execute mode form state)

theorem trace_run_eq (mode : Mode) {state finalState : StringExecution.State mode} {forms : List (StringStack.Form mode)}
    (actual : StringStack.Trace mode state forms finalState) : run mode forms state=finalState := by
  induction actual with
  | nil => rfl
  | step current rest ih => exact ih

theorem owned_run_append (mode : Mode) (start stop : Nat) (first second : List (StringStack.Form mode)) (state : StringExecution.State mode) :
    OwnedRun mode start stop (first++second) state↔OwnedRun mode start stop first state ∧ OwnedRun mode start stop second (run mode first state) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append,OwnedRun,run,true_and]
  | cons form rest ih => simp only [List.cons_append,OwnedRun,run,ih,and_assoc]

theorem run_frame (mode : Mode) (start stop : Nat) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (owned : OwnedRun mode start stop forms state) (position : Nat) (outside : position<start ∨ stop≤position) :
    (run mode forms state).principal.memory position=state.principal.memory position := by
  induction forms generalizing state with
  | nil => rfl
  | cons form rest ih =>
    exact (ih _ owned.2).trans (execute_frame mode start stop form state owned.1 position outside)

theorem native_code_write (mode : Mode) (start stop : Nat) (form : Native.Form mode) (state : StringExecution.State mode)
    (owned : WordOwned mode start stop (Writes.address mode form state.principal)) :
    CodeWrite mode start stop (liftNative mode form) state := by
  have size : (packet mode (liftNative mode form) state).bytes.length=mode.wordBytes := word_encode_length _ _
  unfold CodeWrite
  rw [size]
  exact ⟨by cases mode <;> decide,owned⟩

theorem native_owned_run (mode : Mode) (start stop : Nat) (forms : List (Native.Form mode)) (state : StringExecution.State mode)
    (owned : Writes.OwnedRun mode (WordOwned mode start stop) forms state.principal) :
    OwnedRun mode start stop (forms.map (liftNative mode)) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    exact ⟨native_code_write mode start stop form state owned.1,ih (StringStack.execute mode (liftNative mode form) state) owned.2⟩

end SmcTuring.Native.StringWrites

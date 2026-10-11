module
public import SmcTuring.Native.StringWrites
public import SmcTuring.Native.RegionExecution

public section
namespace SmcTuring.Native.StringReadWindows
open StringWrites MemoryRegion

/-- The single selected data-read window, distinct from decoder probes and
the complete store. Pure stores have no data-read window. -/
structure Window where
  address : Nat
  count : Nat

@[expose] def native (mode : Mode) (form : Native.Form mode) (state : Execution.State mode) : Option Window :=
  (RegionExecution.readAddress mode form state).map fun address => ⟨address.toNat,mode.wordBytes⟩

@[expose] def string (mode : Mode) (form : StringForm.Form mode) (state : StringExecution.State mode) : Option Window :=
  match form with
  | .native form => native mode form state.principal
  | .initialize32 _ _ => none
  | .move width => some ⟨state.sourceIndex.toNat,width⟩
  | _ => some ⟨(StringWrites.string mode form state).address,mode.wordBytes⟩

@[expose] def mixed (mode : Mode) (form : MixedDword.Form mode) (state : Execution.State mode) : Option Window :=
  match form with
  | .arithmetic (.store _ _) => none
  | .arithmetic form => some ⟨(DwordArithmetic.address mode form state).toNat,4⟩
  | .copy (.exchange d) => some ⟨(DwordCode.address mode (.exchange d) state).toNat,4⟩
  | .copy _ => none
  | .wideExchange d => native .x64 (.memory .exchangeAcc d) state

@[expose] def dword (mode : Mode) (form : StringDword.Form mode) (state : StringExecution.State mode) : Option Window :=
  match form with
  | .string form => string mode form state
  | .mixed form => mixed mode form state.principal
  | .xorAccumulator d => some ⟨(DwordXor.address mode d state.principal).toNat,4⟩

@[expose] def control (mode : Mode) (form : StringControl.Form mode) (state : StringExecution.State mode) : Option Window :=
  match form with
  | .previous form => dword mode form state
  | .wideNegation d => some ⟨(WordNegation.address mode d state.principal).toNat,mode.wordBytes⟩

@[expose] def read (mode : Mode) (form : StringStack.Form mode) (state : StringExecution.State mode) : Option Window :=
  match form with
  | .previous form => control mode form state
  | .addSmall d _ => some ⟨(WordAddImmediate.address mode d state.principal).toNat,mode.wordBytes⟩

@[expose] def Contained (region : Region) (window : Option Window) : Prop :=
  match window with
  | none => True
  | some window => region.Contains window.address window.count
@[expose] def Within (mode : Mode) (region : Region) (form : StringStack.Form mode) (state : StringExecution.State mode) : Prop :=
  Contained region (read mode form state)

/-- Indirect memory CALL has a target read distinct from its stack store. -/
@[expose] def NativeLocal (mode : Mode) : Native.Form mode → Prop
  | .memory .callIndirect _ => False
  | _ => True

/-- MOVS reads SI and writes DI; every other added scalar read shares its
complete store window. The classification depends only on the selected form. -/
@[expose] def StringLocal (mode : Mode) : StringForm.Form mode → Prop
  | .native form => NativeLocal mode form
  | .move _ => False
  | _ => True
@[expose] def DwordLocal (mode : Mode) : StringDword.Form mode → Prop
  | .string form => StringLocal mode form
  | _ => True
@[expose] def ControlLocal (mode : Mode) : StringControl.Form mode → Prop
  | .previous form => DwordLocal mode form
  | _ => True
@[expose] def Local (mode : Mode) : StringStack.Form mode → Prop
  | .previous form => ControlLocal mode form
  | _ => True

theorem native_local (mode : Mode) (form : Native.Form mode) (state : Execution.State mode)
    (localRead : NativeLocal mode form) :
    native mode form state=none ∨
      native mode form state=some ⟨(StringWrites.native mode form state).address,(StringWrites.native mode form state).bytes.length⟩ := by
  cases form with
  | moffs address => exact Or.inl rfl
  | exchangeIndirect => right; simp only [native,RegionExecution.readAddress,Option.map_some,StringWrites.native,LittleEndian.word_encode_length];rfl
  | callRelative displacement => exact Or.inl rfl
  | memory operation displacement =>
    cases operation <;> first
      | exact False.elim localRead
      | exact Or.inl rfl
      | right; simp only [native,RegionExecution.readAddress,Option.map_some,StringWrites.native,LittleEndian.word_encode_length];rfl

theorem string_local (mode : Mode) (form : StringForm.Form mode) (state : StringExecution.State mode)
    (localRead : StringLocal mode form) :
    string mode form state=none ∨
      string mode form state=some ⟨(StringWrites.string mode form state).address,(StringWrites.string mode form state).bytes.length⟩ := by
  cases form with
  | native form => exact native_local mode form state.principal localRead
  | initialize32 address value => exact Or.inl rfl
  | move width => exact False.elim localRead
  | exchangeIndex destination d => right;simp only [string,StringWrites.string,LittleEndian.word_encode_length]
  | subtractSmall d value => right;simp only [string,StringWrites.string,LittleEndian.word_encode_length]
  | subtractFull d value => right;simp only [string,StringWrites.string,LittleEndian.word_encode_length]

theorem mixed_local (mode : Mode) (form : MixedDword.Form mode) (state : Execution.State mode) :
    mixed mode form state=none ∨
      mixed mode form state=some ⟨(StringWrites.mixed mode form state).address,(StringWrites.mixed mode form state).bytes.length⟩ := by
  cases form with
  | arithmetic form =>
    cases form <;> first
      | exact Or.inl rfl
      | right;simp only [mixed,StringWrites.mixed,LittleEndian.word_encode_length]
  | copy form =>
    cases form <;> first
      | exact Or.inl rfl
      | right;simp only [mixed,StringWrites.mixed,LittleEndian.word_encode_length]
  | wideExchange d => exact native_local .x64 (.memory .exchangeAcc d) state True.intro

theorem dword_local (mode : Mode) (form : StringDword.Form mode) (state : StringExecution.State mode)
    (localRead : DwordLocal mode form) :
    dword mode form state=none ∨
      dword mode form state=some ⟨(StringWrites.dword mode form state).address,(StringWrites.dword mode form state).bytes.length⟩ := by
  cases form with
  | string form => exact string_local mode form state localRead
  | mixed form => exact mixed_local mode form state.principal
  | xorAccumulator d => right;simp only [dword,StringWrites.dword,LittleEndian.word_encode_length]

theorem control_local (mode : Mode) (form : StringControl.Form mode) (state : StringExecution.State mode)
    (localRead : ControlLocal mode form) :
    control mode form state=none ∨
      control mode form state=some ⟨(StringWrites.control mode form state).address,(StringWrites.control mode form state).bytes.length⟩ := by
  cases form with
  | previous form => exact dword_local mode form state localRead
  | wideNegation d => right;simp only [control,StringWrites.control,LittleEndian.word_encode_length]

theorem read_local (mode : Mode) (form : StringStack.Form mode) (state : StringExecution.State mode)
    (localRead : Local mode form) :
    read mode form state=none ∨
      read mode form state=some ⟨(packet mode form state).address,(packet mode form state).bytes.length⟩ := by
  cases form with
  | previous form => exact control_local mode form state localRead
  | addSmall d value => right;simp only [read,packet,LittleEndian.word_encode_length]

/-- Complete scalar read containment follows from the actual full store
certificate. MOVS and memory-indirect CALL are deliberately excluded here. -/
theorem within_of_owned (mode : Mode) (start stop : Nat) (form : StringStack.Form mode)
    (state : StringExecution.State mode) (localRead : Local mode form)
    (owned : CodeWrite mode start stop form state) : Within mode ⟨start,stop⟩ form state := by
  rcases read_local mode form state localRead with absent | same
  · simp only [Within,Contained,absent]
  · simp only [Within,Contained,same]
    exact ⟨owned.2.1,owned.2.2⟩

end SmcTuring.Native.StringReadWindows

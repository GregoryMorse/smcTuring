module
public import SmcTuring.SMC.ConcreteImage
public import SmcTuring.SMC.VirtualInitialization

public section

namespace SmcTuring.SMC.Concrete

open Dolan

/-- Literal metadata, independently defined from the instruction semantics.
Slots 0..12 are reader pointers to register fields. Further readers point to
the named control words; the pointer reader has an initial scratch-cell target. -/
@[expose] def metadataValue (index : Nat) : Int :=
  if index < 13 then (index : Int) else
    match index with
    | 13 => candidateField
    | 14 => boundaryField
    | 15 => zeroField
    | 16 => resumeField
    | 17 => terminalField
    | 18 => maskField
    | 19 => offsetZeroField
    | 20 => offsetOneField
    | 21 => pointerLabel
    | 22 => heapBase dataLayout.data
    | 23 | 24 => returnField
    | 25 => returnField + 1
    | 28 => heapBase dataLayout.data
    | 31 => terminalPC
    | 35 => kernelPC
    | 37 => 1
    | _ => 0

@[expose] def StaticSlot (index : Nat) : Prop :=
  index < 38 ∧ index ≠ 22 ∧ index ≠ 26 ∧ index ≠ 27 ∧ index ≠ 30 ∧
    index ≠ 32 ∧ index ≠ 33 ∧ index ≠ 34

instance (index : Nat) : Decidable (StaticSlot index) := by unfold StaticSlot; infer_instance

@[expose] def Static (s : State) : Prop :=
  ∀ index, StaticSlot index → s.memory (metaField index) = metadataValue index

@[expose] def initialMemory (source : Mov.State) (field : Int) : Int :=
  if 0 ≤ field then Virtual.dataMemory dataLayout source field
  else metadataValue (-field - 1).toNat

@[expose] def initialState (source : Mov.State) : State :=
  { acc := 0, stack := returnField, pc := kernelPC, carry := false, memory := initialMemory source }

theorem metadata_field_injective : Function.Injective metaField := by
  intro first second equal
  simp only [metaField] at equal
  omega

theorem initialized_metadata (source : Mov.State) (index : Nat) :
    (initialState source).memory (metaField index) = metadataValue index := by
  have negative : ¬ 0 ≤ metaField index := by simp [metaField]
  have coordinate : (-metaField index - 1).toNat = index := by simp [metaField]
  simp only [initialState, initialMemory, negative, ite_false, coordinate]

theorem initial_static (source : Mov.State) : Static (initialState source) := by
  intro index _
  exact initialized_metadata source index

theorem data_nonnegative (field : Int) (code : codeField dataLayout.data field) : 0 ≤ field := by
  rcases code with ⟨index, equal⟩
  simp [dataLayout, fieldAddress] at equal
  omega

theorem initial_rep (source : Mov.State) : Virtual.Rep dataLayout source (initialState source) := by
  have old := Virtual.data_state_correct dataLayout source
  constructor
  · intro r
    have nonnegative := data_nonnegative _ (Virtual.register_is_code dataLayout r)
    simpa only [initialState, initialMemory, Virtual.dataState, nonnegative, ite_true] using old.1 r
  · intro p
    have nonnegative := data_nonnegative _ (heap_is_code dataLayout.data p)
    simpa only [initialState, initialMemory, Virtual.dataState, nonnegative, ite_true] using old.2 p

theorem static_write_frame (s : State) (field datum : Int) (ready : Static s)
    (separate : ∀ index, StaticSlot index → metaField index ≠ field) :
    Static { s with memory := write s.memory field datum } := by
  intro index stable
  simpa [write, separate index stable] using ready index stable

theorem static_dynamic_write (s : State) (index : Nat) (datum : Int) (ready : Static s)
    (dynamic : ¬ StaticSlot index) : Static { s with memory := write s.memory (metaField index) datum } := by
  apply static_write_frame s (metaField index) datum ready
  intro other stable equal
  have same := metadata_field_injective equal
  exact dynamic (same ▸ stable)

theorem static_data_write (s : State) (field datum : Int) (ready : Static s) (nonnegative : 0 ≤ field) :
    Static { s with memory := write s.memory field datum } := by
  apply static_write_frame s field datum ready
  intro index _ equal
  simp only [metaField] at equal
  omega

theorem static_top (s : State) (ready : Static s) : s.memory topField = returnField + 1 := by
  simpa [topField, metadataValue] using ready 25 (by decide)

theorem static_capture (s : State) (sense : Bool) (ready : Static s) : s.memory (captureLabel sense) = returnField := by
  cases sense
  · simpa [captureLabel, metadataValue] using ready 23 (by decide)
  · simpa [captureLabel, metadataValue] using ready 24 (by decide)

theorem initial_register_reader (source : Mov.State) (r : Mov.Register) :
    (initialState source).memory (readerLabel (Four.slot r).val) = Virtual.registerField dataLayout r := by
  rw [readerLabel, initialized_metadata]
  have low := (Four.slot r).isLt
  simp [metadataValue, low, Virtual.registerField, fieldAddress, dataLayout]

end SmcTuring.SMC.Concrete

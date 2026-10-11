module
public import SmcTuring.Native.ConversionEffects

public section
namespace SmcTuring.Native.ConversionImage
open Execution ConversionLayout ConversionEffects ControlImage

@[expose] def reenter (mode : Mode) (layout : Layout) (native : State mode) : State mode :=
  { native with pc := Arithmetic.encodeNat mode layout.start }

theorem initial_intact (mode : Mode) (layout : Layout) (backing : ByteMemory.Memory) :
    Intact mode (entries mode layout) (image mode (entries mode layout) backing) :=
  initialized_intact mode _ _ (separated mode layout)

theorem source_external (mode : Mode) (layout : Layout) (valid : Admissible mode layout) :
    External mode (entries mode layout) (Arithmetic.encodeNat mode layout.source) := by
  apply outside mode layout layout.source _ valid.sourceOutside
  have fits := valid.sourceFits
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  omega

theorem destination_external (mode : Mode) (layout : Layout) (valid : Admissible mode layout) :
    External mode (entries mode layout) (Arithmetic.encodeNat mode layout.destination) := by
  apply outside mode layout layout.destination _ valid.destinationOutside
  have fits := valid.destinationFits
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  omega

theorem swapped_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (intact : Intact mode (entries mode layout) native.memory) (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    Intact mode (entries mode layout) (swapped mode layout native).memory := by
  rw [first_effect mode layout valid native entry]
  have kept := external_store_intact mode _ native.memory intact (Arithmetic.encodeNat mode layout.source) native.accumulator (source_external mode layout valid)
  rwa [source_toNat mode layout valid] at kept

theorem stored_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (intact : Intact mode (entries mode layout) native.memory) (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    Intact mode (entries mode layout) (stored mode layout native).memory := by
  unfold stored
  rw [second_effect mode layout valid _ (swapped_pc mode layout valid native entry)]
  have kept := external_store_intact mode _ (swapped mode layout native).memory (swapped_intact mode layout valid native intact entry)
    (Arithmetic.encodeNat mode layout.destination) (swapped mode layout native).accumulator (destination_external mode layout valid)
  rwa [destination_toNat mode layout valid] at kept

theorem finish_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (intact : Intact mode (entries mode layout) native.memory) (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    Intact mode (entries mode layout) (finish mode layout native).memory := by
  rw [effect mode layout valid native entry]
  have kept := external_store_intact mode _ native.memory intact (Arithmetic.encodeNat mode layout.destination)
    (load mode native.memory (Arithmetic.encodeNat mode layout.source)) (destination_external mode layout valid)
  rwa [destination_toNat mode layout valid] at kept

theorem fetched (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (pc : Nat) (form : Form mode) (member : List.Mem (⟨pc, .fixed form⟩ : Entry mode) (entries mode layout))
    (intact : Intact mode (entries mode layout) native.memory) (location : native.pc = Arithmetic.encodeNat mode pc)
    (below : pc ≤ endPC mode layout) :
    Fetch.fetch mode native.memory native.pc.toNat = some form := by
  rw [location, Arithmetic.encode_nat_toNat mode pc (by have fits := valid.codeFits; omega)]
  exact fetch_current mode ⟨pc, .fixed form⟩ native.memory (intact _ member)

/-- Three forms are fetched from the actual current bytes, including both
exchanges after earlier code/data stores. No future fetch premise is supplied. -/
theorem trace (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (intact : Intact mode (entries mode layout) native.memory) (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    Fetch.Trace mode native (program mode layout) (finish mode layout native) := by
  have firstFetch := fetched mode layout valid native layout.start (first mode layout) (List.Mem.head _) intact entry
    (by unfold endPC thirdPC secondPC; omega)
  have secondFetch := fetched mode layout valid (swapped mode layout native) (secondPC mode layout) (second mode layout)
    (List.Mem.tail _ (List.Mem.head _)) (swapped_intact mode layout valid native intact entry) (swapped_pc mode layout valid native entry)
    (by unfold endPC thirdPC; omega)
  have thirdFetch := fetched mode layout valid (stored mode layout native) (thirdPC mode layout) (third mode layout)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (stored_intact mode layout valid native intact entry) (stored_pc mode layout valid native entry)
    (by unfold endPC; omega)
  exact .step firstFetch (.step secondFetch (.step thirdFetch (.nil _)))

/-- Full-width USEWORD copy: universal current-byte trace, destination value,
source restoration, represented registers/flags, endpoint, intact helper and
exact exterior-byte frame. Data boundaries are not asserted to be pure. -/
theorem correct (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (intact : Intact mode (entries mode layout) native.memory) (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    Fetch.Trace mode native (program mode layout) (finish mode layout native) ∧
    load mode (finish mode layout native).memory (Arithmetic.encodeNat mode layout.destination) = load mode native.memory (Arithmetic.encodeNat mode layout.source) ∧
    load mode (finish mode layout native).memory (Arithmetic.encodeNat mode layout.source) = load mode native.memory (Arithmetic.encodeNat mode layout.source) ∧
    (finish mode layout native).accumulator = native.accumulator ∧
    (finish mode layout native).stack = native.stack ∧
    (finish mode layout native).carry = native.carry ∧
    (finish mode layout native).pc = Arithmetic.encodeNat mode (endPC mode layout) ∧
    Intact mode (entries mode layout) (finish mode layout native).memory ∧
    forall position, ¬ByteMemory.Inside layout.destination mode.wordBytes position -> (finish mode layout native).memory position = native.memory position := by
  refine ⟨trace mode layout valid native intact entry, destination_value mode layout valid native entry,
    source_value mode layout valid native entry, ?_, ?_, ?_, ?_, finish_intact mode layout valid native intact entry,
    frame mode layout valid native entry⟩ <;> rw [effect mode layout valid native entry]

theorem original_image_correct (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (backing : ByteMemory.Memory)
    (native : State mode) (initialized : native.memory = image mode (entries mode layout) backing)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    Fetch.Trace mode native (program mode layout) (finish mode layout native) ∧
    finish mode layout native = { native with
      pc := Arithmetic.encodeNat mode (endPC mode layout),
      memory := ByteMemory.putWord mode native.memory layout.destination (load mode native.memory (Arithmetic.encodeNat mode layout.source)) } ∧
    Intact mode (entries mode layout) (finish mode layout native).memory := by
  have intact : Intact mode (entries mode layout) native.memory := by rw [initialized]; exact initial_intact _ _ _
  exact ⟨trace mode layout valid native intact entry, effect mode layout valid native entry, finish_intact mode layout valid native intact entry⟩

theorem reentry_trace (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (intact : Intact mode (entries mode layout) native.memory) (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    Fetch.Trace mode (reenter mode layout (finish mode layout native)) (program mode layout)
      (finish mode layout (reenter mode layout (finish mode layout native))) :=
  trace mode layout valid _ (finish_intact mode layout valid native intact entry) rfl

theorem reentry_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode) :
    finish mode layout (reenter mode layout native) = { native with
      pc := Arithmetic.encodeNat mode (endPC mode layout),
      memory := ByteMemory.putWord mode native.memory layout.destination (load mode native.memory (Arithmetic.encodeNat mode layout.source)) } :=
  effect mode layout valid _ rfl

end SmcTuring.Native.ConversionImage

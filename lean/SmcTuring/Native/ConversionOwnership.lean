module
public import SmcTuring.Native.ConversionOperands

public section
namespace SmcTuring.Native.ConversionOwnership
open Execution ConversionLayout ConversionEffects ControlImage

theorem first_address (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    Writes.address mode (first mode layout) native = Arithmetic.encodeNat mode layout.source :=
  first_hits mode layout valid native entry

theorem second_address (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode (secondPC mode layout)) :
    Writes.address mode (second mode layout) native = Arithmetic.encodeNat mode layout.destination := by
  have hits := second_hits mode layout valid native entry
  cases mode <;> exact hits

theorem third_address (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode (thirdPC mode layout)) :
    Writes.address mode (third mode layout) native = Arithmetic.encodeNat mode layout.source :=
  third_hits mode layout valid native entry

/-- The actual destination of every reached store is supported on these two
complete words. This theorem makes no claim that ordinary data is code. -/
theorem supported_run (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) (owns : Word mode -> Prop)
    (source : owns (Arithmetic.encodeNat mode layout.source)) (destination : owns (Arithmetic.encodeNat mode layout.destination)) :
    Writes.OwnedRun mode owns (program mode layout) native := by
  change owns (Writes.address mode (first mode layout) native) ∧
    owns (Writes.address mode (second mode layout) (swapped mode layout native)) ∧
    owns (Writes.address mode (third mode layout) (stored mode layout native)) ∧ True
  rw [first_address mode layout valid native entry, second_address mode layout valid _ (swapped_pc mode layout valid native entry),
    third_address mode layout valid _ (stored_pc mode layout valid native entry)]
  exact ⟨source, destination, source, trivial⟩

/-- Both fields must be actual operand windows of owned MOFFS packets. -/
theorem code_owned_run (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) (whole : List (Entry mode))
    (source : Owned mode whole (Arithmetic.encodeNat mode layout.source)) (destination : Owned mode whole (Arithmetic.encodeNat mode layout.destination)) :
    Writes.OwnedRun mode (Owned mode whole) (program mode layout) native :=
  supported_run mode layout valid native entry _ source destination

theorem whole_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) (whole : List (Entry mode))
    (intact : Intact mode whole native.memory) (separate : Separated mode whole)
    (source : Owned mode whole (Arithmetic.encodeNat mode layout.source)) (destination : Owned mode whole (Arithmetic.encodeNat mode layout.destination)) :
    Intact mode whole (finish mode layout native).memory := by
  have kept := run_intact mode whole native (program mode layout) separate intact (code_owned_run mode layout valid native entry whole source destination)
  exact kept

/-- Pure code-to-code copy from original initialized packets. Helper fetches,
code ownership and retained decodability are derived, not supplied as future
trace or intermediate-state assumptions. Geometry is the initial resource. -/
theorem original_image_correct (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) (whole : List (Entry mode)) (backing : ByteMemory.Memory)
    (initialized : native.memory = image mode whole backing) (separate : Separated mode whole)
    (included : forall helper, List.Mem helper (entries mode layout) -> List.Mem helper whole)
    (source : Owned mode whole (Arithmetic.encodeNat mode layout.source)) (destination : Owned mode whole (Arithmetic.encodeNat mode layout.destination)) :
    Fetch.Trace mode native (program mode layout) (finish mode layout native) ∧
    Writes.OwnedRun mode (Owned mode whole) (program mode layout) native ∧
    finish mode layout native = { native with
      pc := Arithmetic.encodeNat mode (endPC mode layout),
      memory := ByteMemory.putWord mode native.memory layout.destination (load mode native.memory (Arithmetic.encodeNat mode layout.source)) } ∧
    Intact mode whole (finish mode layout native).memory := by
  have intact : Intact mode whole native.memory := by rw [initialized]; exact initialized_intact mode whole backing separate
  have helpers : Intact mode (entries mode layout) native.memory := fun helper member => intact helper (included helper member)
  exact ⟨ConversionImage.trace mode layout valid native helpers entry, code_owned_run mode layout valid native entry whole source destination,
    effect mode layout valid native entry, whole_intact mode layout valid native entry whole intact separate source destination⟩

end SmcTuring.Native.ConversionOwnership

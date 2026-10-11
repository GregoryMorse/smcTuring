module
public import SmcTuring.Native.DwordLayout

public section
namespace SmcTuring.Native.DwordEffects
open DwordCode DwordLayout
@[expose] def swapped (mode : Mode) (layout : Layout) (state : Execution.State mode) : Execution.State mode :=
  execute mode (first mode layout) state
@[expose] def stored (mode : Mode) (layout : Layout) (state : Execution.State mode) : Execution.State mode :=
  execute mode (second mode layout) (swapped mode layout state)
@[expose] def finish (mode : Mode) (layout : Layout) (state : Execution.State mode) : Execution.State mode :=
  execute mode (third mode layout) (stored mode layout state)

theorem first_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    swapped mode layout state =
      { state with
        pc := Arithmetic.encodeNat mode (secondPC mode layout)
        accumulator := lift mode (get state.memory layout.source)
        memory := put state.memory layout.source (low mode state.accumulator) } := by
  change { state with
    pc := next mode (first mode layout) state
    accumulator := lift mode (get state.memory (address mode (first mode layout) state).toNat)
    memory := put state.memory (address mode (first mode layout) state).toNat (low mode state.accumulator) } = _
  rw [first_next mode layout state entry,first_hits mode layout valid state entry,source_toNat mode layout valid]

theorem second_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode (secondPC mode layout)) :
    execute mode (second mode layout) state =
      { state with
        pc := Arithmetic.encodeNat mode (thirdPC mode layout)
        memory := put state.memory layout.destination (low mode state.accumulator) } := by
  have primitive : execute mode (second mode layout) state =
      { state with
        pc := next mode (second mode layout) state
        memory := put state.memory (address mode (second mode layout) state).toNat
          (low mode state.accumulator) } := by cases mode <;> rfl
  rw [primitive,second_next mode layout state entry,second_hits mode layout valid state entry,
    destination_toNat mode layout valid]

theorem third_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode (thirdPC mode layout)) :
    execute mode (third mode layout) state =
      { state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        accumulator := lift mode (get state.memory layout.source)
        memory := put state.memory layout.source (low mode state.accumulator) } := by
  change { state with
    pc := next mode (third mode layout) state
    accumulator := lift mode (get state.memory (address mode (third mode layout) state).toNat)
    memory := put state.memory (address mode (third mode layout) state).toNat (low mode state.accumulator) } = _
  rw [third_next mode layout state entry,third_hits mode layout valid state entry,source_toNat mode layout valid]

theorem swapped_pc (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    (swapped mode layout state).pc = Arithmetic.encodeNat mode (secondPC mode layout) := by
  rw [first_effect mode layout valid state entry]

theorem stored_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    stored mode layout state =
      { state with
        pc := Arithmetic.encodeNat mode (thirdPC mode layout)
        accumulator := lift mode (get state.memory layout.source)
        memory := put
          (put state.memory layout.source (low mode state.accumulator))
          layout.destination (get state.memory layout.source) } := by
  rw [stored,second_effect mode layout valid _ (swapped_pc mode layout valid state entry),
    first_effect mode layout valid state entry,low_lift]

theorem stored_pc (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    (stored mode layout state).pc = Arithmetic.encodeNat mode (thirdPC mode layout) := by
  rw [stored_effect mode layout valid state entry]

theorem original_source_read (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (memory : ByteMemory.Memory) (value : Dword) :
    get (put memory layout.destination value) layout.source = get memory layout.source :=
  get_frame memory layout.destination layout.source value (source_outside mode layout valid)

theorem source_read_after_stored (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) :
    get (put
      (put state.memory layout.source (low mode state.accumulator))
      layout.destination (get state.memory layout.source)) layout.source = low mode state.accumulator := by
  rw [original_source_read mode layout valid,get_put]

theorem restored_memory (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (memory : ByteMemory.Memory) (value : Dword) :
    put
      (put (put memory layout.source value)
        layout.destination (get memory layout.source))
      layout.source (get memory layout.source) =
      put memory layout.destination (get memory layout.source) := by
  rw [put_commute _ layout.destination layout.source _ _ (destination_outside mode layout valid),
    put_overwrite,put_get_back]

/-- Exact three-step effect: only the target DWORD changes. EAX is restored;
long-mode writes produce the specified zero-extended RAX, for any entry RAX. -/
theorem effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    finish mode layout state =
      { state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        accumulator := lift mode (low mode state.accumulator)
        memory := put state.memory layout.destination (get state.memory layout.source) } := by
  rw [finish,third_effect mode layout valid _ (stored_pc mode layout valid state entry),
    stored_effect mode layout valid state entry]
  rw [source_read_after_stored mode layout valid state,low_lift,restored_memory mode layout valid state.memory]

theorem destination_value (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    get (finish mode layout state).memory layout.destination = get state.memory layout.source := by
  rw [effect mode layout valid state entry,get_put]

theorem source_value (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    get (finish mode layout state).memory layout.source = get state.memory layout.source := by
  rw [effect mode layout valid state entry,original_source_read mode layout valid]

theorem frame (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (position : Nat) (outside : ¬ByteMemory.Inside layout.destination 4 position) :
    (finish mode layout state).memory position = state.memory position := by
  rw [effect mode layout valid state entry]
  apply ByteMemory.put_frame
  change ¬ByteMemory.Inside layout.destination 4 position
  exact outside

theorem registers (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    (finish mode layout state).accumulator = lift mode (low mode state.accumulator) ∧
      (finish mode layout state).stack = state.stack ∧ (finish mode layout state).carry = state.carry := by
  rw [effect mode layout valid state entry]
  exact ⟨rfl,rfl,rfl⟩

theorem x86_accumulator (layout : Layout) (valid : Admissible .x86 layout)
    (state : Execution.State .x86) (entry : state.pc = Arithmetic.encodeNat .x86 layout.start) :
    (finish .x86 layout state).accumulator = state.accumulator := by
  rw [effect .x86 layout valid state entry,lift_low_x86]

theorem x64_zero_extension (layout : Layout) (valid : Admissible .x64 layout)
    (state : Execution.State .x64) (entry : state.pc = Arithmetic.encodeNat .x64 layout.start) :
    (finish .x64 layout state).accumulator.toNat < 2^32 := by
  rw [effect .x64 layout valid state entry]
  exact lift_low_x64_bound state.accumulator

end SmcTuring.Native.DwordEffects

module
public import SmcTuring.Native.AccumulatorLayout

public section
namespace SmcTuring.Native.AccumulatorEffects
open Execution AccumulatorLayout

@[expose] def saved (mode : Mode) (layout : Layout) (state : State mode) : State mode :=
  execute mode (saveForm mode layout) state
@[expose] def swapped (mode : Mode) (layout : Layout) (state : State mode) : State mode :=
  Reader.swapped mode state (firstDisp mode layout)
@[expose] def restored (mode : Mode) (layout : Layout) (state : State mode) : State mode :=
  Reader.restored mode state (Arithmetic.encodeNat mode layout.pointer) (firstDisp mode layout) (secondDisp mode layout)
@[expose] def finish (mode : Mode) (layout : Layout) (state : State mode) : State mode :=
  Reader.swapped mode (restored mode layout state) (thirdDisp mode layout)

theorem state_ext (mode : Mode) (first second : State mode)
    (pc : first.pc = second.pc) (accumulator : first.accumulator = second.accumulator)
    (stack : first.stack = second.stack) (carry : first.carry = second.carry)
    (memory : first.memory = second.memory) : first = second := by
  cases first; cases second; simp_all

theorem save_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.prologue) :
    saved mode layout state = {state with
      pc := Arithmetic.encodeNat mode (savedPC mode layout)
      memory := ByteMemory.putWord mode state.memory layout.save state.accumulator} := by
  rw [saved,saveForm,Reader.store_effect mode state _ _ (save_hits mode layout valid state entry)]
  change {state with
      pc := nextPC mode (saveForm mode layout) state
      memory := ByteMemory.putWord mode state.memory (Arithmetic.encodeNat mode layout.save).toNat state.accumulator} = _
  rw [save_next mode layout state entry,save_toNat mode layout valid]

theorem saved_value (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.prologue) :
    load mode (saved mode layout state).memory (Arithmetic.encodeNat mode layout.save) = state.accumulator := by
  rw [save_effect mode layout valid state entry]
  have loaded := load_put_word mode state.memory (Arithmetic.encodeNat mode layout.save) state.accumulator
  rwa [save_toNat mode layout valid] at loaded

theorem saved_pointer (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.prologue) :
    load mode (saved mode layout state).memory (Arithmetic.encodeNat mode layout.pointer) =
      load mode state.memory (Arithmetic.encodeNat mode layout.pointer) := by
  rw [save_effect mode layout valid state entry]
  have framed := Writes.load_frame mode state.memory (Arithmetic.encodeNat mode layout.save)
    (Arithmetic.encodeNat mode layout.pointer) state.accumulator
    (fun index => by rw [save_toNat mode layout valid,pointer_toNat mode layout valid]; exact save_pointer_apart mode layout valid index)
  rwa [save_toNat mode layout valid] at framed

theorem swapped_pc (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    (swapped mode layout state).pc = Arithmetic.encodeNat mode (secondPC mode layout) := by
  rw [swapped,Reader.exchange_effect mode state _ _ (first_hits mode layout valid state entry)]
  exact first_next mode layout state entry

theorem restored_pc (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    (restored mode layout state).pc = Arithmetic.encodeNat mode (thirdPC mode layout) := by
  change (execute mode (second mode layout) (swapped mode layout state)).pc = _
  change (execute mode (Reader.storeForm mode (Arithmetic.encodeNat mode layout.pointer) (secondDisp mode layout))
    (swapped mode layout state)).pc = _
  rw [Reader.store_effect mode _ _ _ (second_hits mode layout valid _ (swapped_pc mode layout valid state entry))]
  exact second_next mode layout _ (swapped_pc mode layout valid state entry)

theorem restored_memory (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    (restored mode layout state).memory = state.memory :=
  Reader.restored_memory mode state _ _ _ (first_hits mode layout valid state entry)
    (second_hits mode layout valid _ (swapped_pc mode layout valid state entry))

theorem restored_accumulator (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    (restored mode layout state).accumulator = load mode state.memory (Arithmetic.encodeNat mode layout.pointer) :=
  Reader.restored_accumulator mode state _ _ _ (first_hits mode layout valid state entry)
    (second_hits mode layout valid _ (swapped_pc mode layout valid state entry))

theorem restored_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    restored mode layout state = {state with
      pc := Arithmetic.encodeNat mode (thirdPC mode layout)
      accumulator := load mode state.memory (Arithmetic.encodeNat mode layout.pointer)} := by
  apply state_ext
  · exact restored_pc mode layout valid state entry
  · exact restored_accumulator mode layout valid state entry
  · cases mode <;> rfl
  · cases mode <;> rfl
  · exact restored_memory mode layout valid state entry

theorem effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    finish mode layout state = {state with
      pc := Arithmetic.encodeNat mode (endPC mode layout)
      accumulator := load mode state.memory (Arithmetic.encodeNat mode layout.save)
      memory := ByteMemory.putWord mode state.memory layout.save
        (load mode state.memory (Arithmetic.encodeNat mode layout.pointer))} := by
  rw [finish,Reader.exchange_effect mode _ _ _ (third_hits mode layout valid _ (restored_pc mode layout valid state entry))]
  have next := third_next mode layout (restored mode layout state) (restored_pc mode layout valid state entry)
  change nextPC mode (.memory .exchangeAcc (thirdDisp mode layout)) (restored mode layout state) = _ at next
  rw [next,restored_effect mode layout valid state entry,save_toNat mode layout valid]

/-- The body may change arbitrary other memory and AX. Its saved entry word
and pointer are the two reserved full-width field invariants. -/
theorem correct (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) (original : Word mode)
    (saved : load mode state.memory (Arithmetic.encodeNat mode layout.save) = original)
    (pointer : load mode state.memory (Arithmetic.encodeNat mode layout.pointer) = Arithmetic.encodeNat mode layout.save) :
    finish mode layout state = {state with
      pc := Arithmetic.encodeNat mode (endPC mode layout)
      accumulator := original
      memory := ByteMemory.putWord mode state.memory layout.save (Arithmetic.encodeNat mode layout.save)} := by
  rw [effect mode layout valid state entry,saved,pointer]

theorem reset_value (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.save) =
      load mode state.memory (Arithmetic.encodeNat mode layout.pointer) := by
  rw [effect mode layout valid state entry]
  have loaded := load_put_word mode state.memory (Arithmetic.encodeNat mode layout.save)
    (load mode state.memory (Arithmetic.encodeNat mode layout.pointer))
  rwa [save_toNat mode layout valid] at loaded

theorem pointer_value (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.pointer) =
      load mode state.memory (Arithmetic.encodeNat mode layout.pointer) := by
  rw [effect mode layout valid state entry]
  have framed := Writes.load_frame mode state.memory (Arithmetic.encodeNat mode layout.save)
    (Arithmetic.encodeNat mode layout.pointer) (load mode state.memory (Arithmetic.encodeNat mode layout.pointer))
    (fun index => by rw [save_toNat mode layout valid,pointer_toNat mode layout valid]; exact save_pointer_apart mode layout valid index)
  rwa [save_toNat mode layout valid] at framed

theorem frame (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (state : State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.epilogue) (position : Nat)
    (outside : ¬ByteMemory.Inside layout.save mode.wordBytes position) :
    (finish mode layout state).memory position = state.memory position := by
  rw [effect mode layout valid state entry]
  exact ByteMemory.put_frame _ _ _ _ (by simpa using outside)

end SmcTuring.Native.AccumulatorEffects

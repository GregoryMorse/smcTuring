module
public import SmcTuring.Native.Writes
public import SmcTuring.Native.Protected

public section
namespace SmcTuring.Native.StringCopy
open ByteMemory

structure State where
  source : Nat
  destination : Nat
  memory : Memory

/-- Selected forward MOVS effect with DF=0 and no address wrapping. This reads
the current bytes before storing the complete 1/2/4/8-byte element. -/
@[expose] def execute (width : Nat) (state : State) : State :=
  ⟨state.source + width, state.destination + width,
    putBytes state.memory state.destination (bytesAt state.memory state.source width)⟩
@[expose] def run : List Nat -> State -> State
  | [], state => state
  | width :: rest, state => run rest (execute width state)
@[expose] def count (widths : List Nat) : Nat := widths.sum
@[expose] def Apart (source destination size : Nat) : Prop :=
  source + size ≤ destination ∨ destination + size ≤ source

/-- Two consecutive stores equal one store of their concatenated bytes. -/
theorem adjacent_put (memory : Memory) (address : Nat) (first second : List LittleEndian.Byte) :
    putBytes (putBytes memory address first) (address + first.length) second =
      putBytes memory address (first ++ second) := by
  funext position
  by_cases before : position < address
  · have a : ¬Inside address first.length position := by unfold Inside; omega
    have b : ¬Inside (address + first.length) second.length position := by unfold Inside; omega
    have c : ¬Inside address (first ++ second).length position := by simp only [Inside, List.length_append]; omega
    rw [put_frame _ _ _ _ b, put_frame _ _ _ _ a, put_frame _ _ _ _ c]
  · by_cases early : position < address + first.length
    · have a : Inside address first.length position := by unfold Inside; omega
      have b : ¬Inside (address + first.length) second.length position := by unfold Inside; omega
      have c : Inside address (first.length + second.length) position := by unfold Inside; omega
      have index : position - address < first.length := by omega
      rw [put_frame _ _ _ _ b]
      simp [putBytes, List.length_append, a, c, List.getElem_append_left index]
    · by_cases late : position < address + first.length + second.length
      · have b : Inside (address + first.length) second.length position := by unfold Inside; omega
        have c : Inside address (first.length + second.length) position := by unfold Inside; omega
        have index : first.length ≤ position - address := by omega
        simp [putBytes, List.length_append, b, c, List.getElem_append_right index, Nat.sub_sub]
      · have a : ¬Inside address first.length position := by unfold Inside; omega
        have b : ¬Inside (address + first.length) second.length position := by unfold Inside; omega
        have c : ¬Inside address (first ++ second).length position := by simp only [Inside, List.length_append]; omega
        rw [put_frame _ _ _ _ b, put_frame _ _ _ _ a, put_frame _ _ _ _ c]

theorem empty_put (memory : Memory) (address : Nat) : putBytes memory address [] = memory := by
  funext position
  exact put_frame _ _ _ _ (by simp [Inside])

theorem apart_tail (source destination first rest : Nat) (separate : Apart source destination (first + rest)) :
    Apart (source + first) (destination + first) rest := by
  unfold Apart at *
  rcases separate with left | right <;> omega

theorem source_outside (source destination size : Nat) (separate : Apart source destination size) (index : Fin size) :
    ¬Inside destination size (source + index.val) := by
  have small := index.isLt
  unfold Apart at separate
  unfold Inside
  rcases separate with left | right <;> omega

theorem tail_read (memory : Memory) (source destination first rest : Nat) (separate : Apart source destination (first + rest)) :
    bytesAt (putBytes memory destination (bytesAt memory source first)) (source + first) rest =
      bytesAt memory (source + first) rest := by
  apply bytes_at_frame
  intro index
  have small := index.isLt
  simp only [bytes_at_length]
  unfold Apart at separate
  unfold Inside
  rcases separate with left | right <;> omega

/-- Exact byte-copy result for every finite width sequence. Source/destination
non-overlap is a static interval premise; no intermediate read is assumed. -/
theorem effect (widths : List Nat) (state : State) (separate : Apart state.source state.destination (count widths)) :
    run widths state = ⟨state.source + count widths, state.destination + count widths,
      putBytes state.memory state.destination (bytesAt state.memory state.source (count widths))⟩ := by
  induction widths generalizing state with
  | nil => simp only [run, count, List.sum_nil, Nat.add_zero, bytesAt, List.ofFn_zero, empty_put]
  | cons first rest ih =>
    have split : count (first :: rest) = first + count rest := rfl
    have tail := ih (execute first state) (apart_tail state.source state.destination first (count rest) (by simpa only [split] using separate))
    rw [run, tail]
    change (⟨(state.source + first) + count rest, (state.destination + first) + count rest,
      putBytes (putBytes state.memory state.destination (bytesAt state.memory state.source first))
        (state.destination + first) (bytesAt (putBytes state.memory state.destination (bytesAt state.memory state.source first))
          (state.source + first) (count rest))⟩ : State) = _
    rw [tail_read state.memory state.source state.destination first (count rest) (by simpa only [split] using separate)]
    have adjacent := adjacent_put state.memory state.destination (bytesAt state.memory state.source first) (bytesAt state.memory (state.source + first) (count rest))
    rw [bytes_at_length] at adjacent
    rw [adjacent, ←Protected.bytes_at_append, ←split]
    simp only [split, Nat.add_assoc]

theorem copied (widths : List Nat) (state : State) (separate : Apart state.source state.destination (count widths)) :
    bytesAt (run widths state).memory state.destination (count widths) = bytesAt state.memory state.source (count widths) := by
  rw [effect widths state separate]
  simpa only [bytes_at_length] using bytes_at_put state.memory state.destination (bytesAt state.memory state.source (count widths))

theorem source_preserved (widths : List Nat) (state : State) (separate : Apart state.source state.destination (count widths)) :
    bytesAt (run widths state).memory state.source (count widths) = bytesAt state.memory state.source (count widths) := by
  rw [effect widths state separate]
  apply bytes_at_frame
  simpa only [bytes_at_length] using source_outside state.source state.destination (count widths) separate

theorem frame (widths : List Nat) (state : State) (separate : Apart state.source state.destination (count widths)) (position : Nat)
    (outside : ¬Inside state.destination (count widths) position) :
    (run widths state).memory position = state.memory position := by
  rw [effect widths state separate]
  exact put_frame _ _ _ _ (by simpa using outside)

theorem run_append (first second : List Nat) (state : State) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons head rest ih => exact ih (execute head state)

end SmcTuring.Native.StringCopy

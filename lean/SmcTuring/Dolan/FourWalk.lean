module
public import SmcTuring.Dolan.FourRegisters

public section

namespace SmcTuring.Dolan.Four

open Mov (Word Memory)

theorem run_append (first second : List Instruction) (s : State) :
    run (first ++ second) s = (run first s).bind (run second) := by
  induction first generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.cons_append, run]
    cases h : execute i s <;> simp [ih]

theorem run_composition {first second : List Instruction} {s middle finish : State}
    (a : run first s = some middle) (b : run second middle = some finish) :
    run (first ++ second) s = some finish := by
  calc
    _ = (run first s).bind (run second) := run_append first second s
    _ = (some middle).bind (run second) := congrArg (fun result : Option State => result.bind (run second)) a
    _ = some finish := b

@[expose] def RingLinks (memory : Memory) : Prop :=
  ∀ i : Fin 13, memory (i.val, true) = .address ((i.val + 1) % 13)

@[expose] def ringResult (s : State) (position : Nat) : State :=
  { s with registers := write s.registers .ring (.address (position % 13)) }

theorem ring_loads_correct (s : State) (temporary : Register) (position count : Nat)
    (different : temporary ≠ .ring) (links : RingLinks s.memory)
    (hr : s.registers .ring = .address (position % 13))
    (ht : s.registers temporary = .offset true) :
    run (List.replicate count (.load .ring .ring temporary)) s = some (ringResult s (position + count)) := by
  induction count generalizing s position with
  | zero =>
    have same : write s.registers .ring (.address (position % 13)) = s.registers := by
      rw [← hr]
      exact write_back s.registers .ring
    simp [run, ringResult, same]
  | succ count ih =>
    let middle := ringResult s (position + 1)
    have next := links ⟨position % 13, Nat.mod_lt _ (by decide)⟩
    have first : execute (.load .ring .ring temporary) s = some middle := by
      simpa [execute, address, hr, ht, middle, ringResult, Nat.add_mod] using
        congrArg (fun value : Word => some ({ s with registers := write s.registers .ring value } : State)) next
    have mr : middle.registers .ring = .address ((position + 1) % 13) := by simp [middle, ringResult, write]
    have mt : middle.registers temporary = .offset true := by simp [middle, ringResult, write, different, ht]
    have tail := ih middle (position + 1) links mr mt
    have result : ringResult middle (position + 1 + count) = ringResult s (position + (count + 1)) := by
      have sum : position + 1 + count = position + (count + 1) := by omega
      simp [ringResult, middle, write_overwrite, sum]
    simp only [List.replicate_succ, run, first, Option.bind_some]
    exact tail.trans (congrArg some result)

@[expose] def walkResult (s : State) (temporary : Register) (destination : Fin 13) : State :=
  { s with registers := write (write s.registers temporary (.offset true)) .ring (.address destination.val) }

theorem walk_correct (s : State) (temporary : Register) (origin destination : Fin 13)
    (different : temporary ≠ .ring) (links : RingLinks s.memory)
    (hr : s.registers .ring = .address origin.val) :
    run (walk temporary origin destination) s = some (walkResult s temporary destination) := by
  let prepared : State := { s with registers := write s.registers temporary (.offset true) }
  have first : run [.immediate temporary (.offset true)] s = some prepared := rfl
  have pr : prepared.registers .ring = .address (origin.val % 13) := by
    simp [prepared, write, Ne.symm different, hr, Nat.mod_eq_of_lt origin.isLt]
  have pt : prepared.registers temporary = .offset true := by simp [prepared, write]
  have tail := ring_loads_correct prepared temporary origin.val (distance origin destination) different links pr pt
  have equal : ringResult prepared (origin.val + distance origin destination) = walkResult s temporary destination := by
    simp only [ringResult, distance_correct, prepared, walkResult]
  exact run_composition first (tail.trans (congrArg some equal))

theorem walk_register_frame (s : State) (temporary r : Register) (destination : Fin 13)
    (ht : r ≠ temporary) (hr : r ≠ .ring) :
    (walkResult s temporary destination).registers r = s.registers r := by simp [walkResult, write, ht, hr]

end SmcTuring.Dolan.Four

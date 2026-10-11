module
public import SmcTuring.Dolan.FourWalk

public section

namespace SmcTuring.Dolan.Four

open Mov (Word Memory)

@[expose] def fetchResult (s : State) (temporary : Register) (destination : Fin 13) (value : Word) : State :=
  let walked := walkResult s temporary destination
  { walked with registers := write walked.registers temporary value }

theorem fetch_correct (source : Mov.State) (target : State) (origin : Fin 13)
    (r : Mov.Register) (temporary : Register) (different : temporary ≠ .ring)
    (rep : Coherent source target origin) :
    run (fetch temporary origin r) target =
      some (fetchResult target temporary (slot r) (encode (source.registers r))) := by
  let walked := walkResult target temporary (slot r)
  have first : run (walk temporary origin (slot r)) target = some walked :=
    walk_correct target temporary origin (slot r) different rep.2.2.1 rep.1
  have wr : walked.registers .ring = .address (slot r).val := by simp [walked, walkResult, write]
  have payload : walked.memory ((slot r).val, false) = encode (source.registers r) := rep.2.1 r
  have tail : run [.immediate temporary (.offset false), .load temporary .ring temporary] walked =
      some (fetchResult target temporary (slot r) (encode (source.registers r))) := by
    simp [run, execute, address, write, Ne.symm different, wr, payload, fetchResult]
    exact ⟨rfl, rfl⟩
  exact run_composition first tail

theorem fetch_result_coherent (source : Mov.State) (target : State) (origin : Fin 13)
    (r : Mov.Register) (temporary : Register) (different : temporary ≠ .ring)
    (rep : Coherent source target origin) :
    Coherent source (fetchResult target temporary (slot r) (encode (source.registers r))) (slot r) := by
  refine ⟨?_, rep.2⟩
  simp [fetchResult, walkResult, write, Ne.symm different]

theorem fetch_value (target : State) (temporary : Register) (destination : Fin 13) (value : Word) :
    (fetchResult target temporary destination value).registers temporary = value := by
  simp [fetchResult, write]

theorem fetch_register_frame (target : State) (temporary r : Register) (destination : Fin 13) (value : Word)
    (ht : r ≠ temporary) (hr : r ≠ .ring) :
    (fetchResult target temporary destination value).registers r = target.registers r := by
  simp [fetchResult, walkResult, write, ht, hr]

@[expose] def spillResult (s : State) (temporary value : Register) (destination : Fin 13) : State :=
  let walked := walkResult s temporary destination
  { registers := write walked.registers temporary (.offset false)
    memory := write s.memory (destination.val, false) (s.registers value) }

theorem spill_correct (s : State) (temporary value : Register) (origin destination : Fin 13)
    (different : temporary ≠ .ring) (valueTemp : value ≠ temporary) (valueRing : value ≠ .ring)
    (links : RingLinks s.memory) (hr : s.registers .ring = .address origin.val) :
    run (walk temporary origin destination ++
      [.immediate temporary (.offset false), .store .ring temporary value]) s =
      some (spillResult s temporary value destination) := by
  let walked := walkResult s temporary destination
  have first : run (walk temporary origin destination) s = some walked :=
    walk_correct s temporary origin destination different links hr
  have wr : walked.registers .ring = .address destination.val := by simp [walked, walkResult, write]
  have wv : walked.registers value = s.registers value :=
    walk_register_frame s temporary value destination valueTemp valueRing
  have tail : run [.immediate temporary (.offset false), .store .ring temporary value] walked =
      some (spillResult s temporary value destination) := by
    simp [run, execute, address, write, Ne.symm different, valueTemp, wr, wv, spillResult]
    exact ⟨rfl, rfl⟩
  exact run_composition first tail

theorem spill_result_coherent (source : Mov.State) (target : State) (origin : Fin 13)
    (r : Mov.Register) (temporary value : Register) (word : Word) (different : temporary ≠ .ring)
    (rep : Coherent source target origin) (hv : target.registers value = encode word) :
    Coherent { source with registers := write source.registers r word }
      (spillResult target temporary value (slot r)) (slot r) := by
  have registers : Coherent source
      { target with registers := (spillResult target temporary value (slot r)).registers } (slot r) := by
    refine ⟨?_, rep.2⟩
    simp [spillResult, walkResult, write, Ne.symm different]
  have updated := spill_coherent source _ (slot r) r word registers
  simpa [spillResult, hv] using updated

theorem reset_coherent (source : Mov.State) (target : State) (origin : Fin 13)
    (temporary : Register) (different : temporary ≠ .ring) (rep : Coherent source target origin) :
    ∃ finish, run (reset temporary origin) target = some finish ∧
      Coherent source finish ⟨0, by decide⟩ := by
  refine ⟨walkResult target temporary ⟨0, by decide⟩,
    walk_correct target temporary origin _ different rep.2.2.1 rep.1, ?_⟩
  exact ⟨by simp [walkResult, write], rep.2⟩

end SmcTuring.Dolan.Four

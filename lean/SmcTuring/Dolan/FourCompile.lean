module
public import SmcTuring.Dolan.FourOperations

public section

namespace SmcTuring.Dolan.Four

open Mov (Word Memory)

theorem free_register_coherent (source : Mov.State) (target : State) (origin : Fin 13)
    (r : Register) (value : Word) (different : r ≠ .ring) (rep : Coherent source target origin) :
    Coherent source { target with registers := write target.registers r value } origin := by
  exact ⟨by simp [write, Ne.symm different, rep.1], rep.2⟩

theorem encoded_address (source : Mov.State) (target : State) (base offset : Mov.Register)
    (hb : target.registers .a = encode (source.registers base))
    (ho : target.registers .b = encode (source.registers offset)) :
    address target .a .b = (Mov.address source base offset).map (fun p => (p.1 + 13, p.2)) := by
  simp only [address, hb, ho, Mov.address]
  cases source.registers base <;> cases source.registers offset <;> rfl

/-- Operand fetches preserve the already fetched operands. Keep their outputs
abstract so the full compiler proof does not expand every ring load. -/
theorem fetch_base_offset (source : Mov.State) (target : State) (base offset : Mov.Register)
    (rep : Coherent source target ⟨0, by decide⟩) :
    ∃ finish, run (fetch .a ⟨0, by decide⟩ base ++ fetch .b (slot base) offset) target = some finish ∧
      Coherent source finish (slot offset) ∧ finish.registers .a = encode (source.registers base) ∧
      finish.registers .b = encode (source.registers offset) := by
  let first := fetchResult target .a (slot base) (encode (source.registers base))
  have loadedBase : run (fetch .a ⟨0, by decide⟩ base) target = some first :=
    fetch_correct source target _ base .a (by decide) rep
  have firstRep : Coherent source first (slot base) := fetch_result_coherent source target _ base .a (by decide) rep
  let finish := fetchResult first .b (slot offset) (encode (source.registers offset))
  have loadedOffset : run (fetch .b (slot base) offset) first = some finish :=
    fetch_correct source first _ offset .b (by decide) firstRep
  have represented := fetch_result_coherent source first _ offset .b (by decide) firstRep
  have baseKept : finish.registers .a = encode (source.registers base) :=
    (fetch_register_frame first .b .a _ _ (by decide) (by decide)).trans (fetch_value target .a _ _)
  exact ⟨finish, run_composition loadedBase loadedOffset, represented, baseKept, fetch_value first .b _ _⟩

theorem fetch_store_operands (source : Mov.State) (target : State) (base offset sourceReg : Mov.Register)
    (rep : Coherent source target ⟨0, by decide⟩) :
    ∃ finish, run ((fetch .a ⟨0, by decide⟩ base ++ fetch .b (slot base) offset) ++
        fetch .c (slot offset) sourceReg) target = some finish ∧
      Coherent source finish (slot sourceReg) ∧ finish.registers .a = encode (source.registers base) ∧
      finish.registers .b = encode (source.registers offset) ∧
      finish.registers .c = encode (source.registers sourceReg) := by
  rcases fetch_base_offset source target base offset rep with ⟨middle, completed, represented, hb, ho⟩
  let finish := fetchResult middle .c (slot sourceReg) (encode (source.registers sourceReg))
  have loaded := fetch_correct source middle (slot offset) sourceReg .c (by decide) represented
  have finishRep := fetch_result_coherent source middle (slot offset) sourceReg .c (by decide) represented
  have baseKept := (fetch_register_frame middle .c .a (slot sourceReg)
    (encode (source.registers sourceReg)) (by decide) (by decide)).trans hb
  have offsetKept := (fetch_register_frame middle .c .b (slot sourceReg)
    (encode (source.registers sourceReg)) (by decide) (by decide)).trans ho
  exact ⟨finish, run_composition completed loaded, finishRep, baseKept, offsetKept, fetch_value middle .c _ _⟩

theorem spill_and_reset (source : Mov.State) (target : State) (origin : Fin 13)
    (dest : Mov.Register) (value : Word) (rep : Coherent source target origin)
    (hv : target.registers .a = encode value) :
    ∃ finish, run (spill .b .a origin dest ++ reset .b (slot dest)) target = some finish ∧
      Coherent { source with registers := write source.registers dest value } finish ⟨0, by decide⟩ := by
  let spilled := spillResult target .b .a (slot dest)
  have stored : run (spill .b .a origin dest) target = some spilled :=
    spill_correct target .b .a origin (slot dest) (by decide) (by decide) (by decide) rep.2.2.1 rep.1
  have spilledRep := spill_result_coherent source target origin dest .b .a value (by decide) rep hv
  rcases reset_coherent _ spilled (slot dest) .b (by decide) spilledRep with ⟨finish, resetRun, finishRep⟩
  exact ⟨finish, run_composition stored resetRun, finishRep⟩

/-- Every successful source MOV is implemented by a finite, four-register
MOV block. The block restores the ring cursor and permits arbitrary source
operand/destination aliasing. -/
theorem compile_instruction_correct (i : Mov.Instruction) (source next : Mov.State) (target : State)
    (rep : Coherent source target ⟨0, by decide⟩) (completed : Mov.execute i source = some next) :
    ∃ finish, run (compileInstruction i) target = some finish ∧ Coherent next finish ⟨0, by decide⟩ := by
  cases i with
  | immediate dest value =>
    have sourceEq : next = { source with registers := write source.registers dest value } := by
      exact (Option.some.inj completed).symm
    subst next
    let prepared : State := { target with registers := write target.registers .a (encode value) }
    have first : run [.immediate .a (encode value)] target = some prepared := rfl
    have preparedRep : Coherent source prepared ⟨0, by decide⟩ :=
      free_register_coherent source target _ .a _ (by decide) rep
    have valueReady : prepared.registers .a = encode value := by simp [prepared, write]
    rcases spill_and_reset source prepared _ dest value preparedRep valueReady with ⟨finish, tail, represented⟩
    refine ⟨finish, ?_, represented⟩
    simpa only [compileInstruction, List.append_assoc] using run_composition first tail
  | load dest base offset =>
    cases location : Mov.address source base offset with
    | none => simp [Mov.execute, location] at completed
    | some p =>
      have sourceEq : next = { source with registers := write source.registers dest (source.memory p) } := by
        exact (Option.some.inj (by simpa [Mov.execute, location] using completed)).symm
      subst next
      rcases fetch_base_offset source target base offset rep with ⟨fetched, first, fetchedRep, hb, ho⟩
      have targetLocation : address fetched .a .b = some (p.1 + 13, p.2) := by
        simpa [location] using encoded_address source fetched base offset hb ho
      let loaded : State := { fetched with registers := write fetched.registers .a (encode (source.memory p)) }
      have payload := fetchedRep.2.2.2 p
      have loadedRun : run [.load .a .a .b] fetched = some loaded := by
        simp [run, execute, targetLocation, loaded, payload]
      have loadedRep : Coherent source loaded (slot offset) :=
        free_register_coherent source fetched _ .a _ (by decide) fetchedRep
      have valueReady : loaded.registers .a = encode (source.memory p) := by simp [loaded, write]
      rcases spill_and_reset source loaded (slot offset) dest (source.memory p) loadedRep valueReady with
        ⟨finish, tail, represented⟩
      refine ⟨finish, ?_, represented⟩
      simpa only [compileInstruction, List.append_assoc] using
        run_composition first (run_composition loadedRun tail)
  | store base offset sourceReg =>
    cases location : Mov.address source base offset with
    | none => simp [Mov.execute, location] at completed
    | some p =>
      have sourceEq : next = { source with memory := write source.memory p (source.registers sourceReg) } := by
        exact (Option.some.inj (by simpa [Mov.execute, location] using completed)).symm
      subst next
      rcases fetch_store_operands source target base offset sourceReg rep with
        ⟨fetched, first, fetchedRep, hb, ho, hv⟩
      have targetLocation : address fetched .a .b = some (p.1 + 13, p.2) := by
        simpa [location] using encoded_address source fetched base offset hb ho
      let stored : State := { fetched with memory := write fetched.memory (p.1 + 13, p.2) (encode (source.registers sourceReg)) }
      have storedRun : run [.store .a .b .c] fetched = some stored := by
        simp [run, execute, targetLocation, stored, hv]
      have storedRep : Coherent { source with memory := write source.memory p (source.registers sourceReg) }
          stored (slot sourceReg) := heap_store_coherent source fetched _ p _ fetchedRep
      rcases reset_coherent _ stored (slot sourceReg) .a (by decide) storedRep with ⟨finish, tail, represented⟩
      refine ⟨finish, ?_, represented⟩
      simpa only [compileInstruction, List.append_assoc] using
        run_composition first (run_composition storedRun tail)

theorem run_after_failure (first second : List Instruction) (target : State)
    (fault : run first target = none) : run (first ++ second) target = none := by
  rw [run_append, fault]
  rfl

theorem run_completed_failure {first second : List Instruction} {target middle : State}
    (completed : run first target = some middle) (fault : run second middle = none) :
    run (first ++ second) target = none := by
  calc
    _ = (run first target).bind (run second) := run_append first second target
    _ = (some middle).bind (run second) := congrArg (fun result : Option State => result.bind (run second)) completed
    _ = none := fault

/-- An invalid source dereference reaches the corresponding target
dereference and traps. The ring walk and operand fetches cannot invent a halt. -/
theorem compile_instruction_fault (i : Mov.Instruction) (source : Mov.State) (target : State)
    (rep : Coherent source target ⟨0, by decide⟩) (fault : Mov.execute i source = none) :
    run (compileInstruction i) target = none := by
  cases i with
  | immediate dest word => simp [Mov.execute] at fault
  | load dest base offset =>
    cases location : Mov.address source base offset with
    | some p => simp [Mov.execute, location] at fault
    | none =>
      rcases fetch_base_offset source target base offset rep with ⟨fetched, first, _, hb, ho⟩
      have targetLocation : address fetched .a .b = none := by
        simpa [location] using encoded_address source fetched base offset hb ho
      have stopped : run [.load .a .a .b] fetched = none := by simp [run, execute, targetLocation]
      have tail := run_after_failure [.load .a .a .b]
        (spill .b .a (slot offset) dest ++ reset .b (slot dest)) fetched stopped
      simpa only [compileInstruction, List.append_assoc] using run_completed_failure first tail
  | store base offset sourceReg =>
    cases location : Mov.address source base offset with
    | some p => simp [Mov.execute, location] at fault
    | none =>
      rcases fetch_store_operands source target base offset sourceReg rep with ⟨fetched, first, _, hb, ho, _⟩
      have targetLocation : address fetched .a .b = none := by
        simpa [location] using encoded_address source fetched base offset hb ho
      have stopped : run [.store .a .b .c] fetched = none := by simp [run, execute, targetLocation]
      have tail := run_after_failure [.store .a .b .c] (reset .a (slot sourceReg)) fetched stopped
      simpa only [compileInstruction, List.append_assoc] using run_completed_failure first tail

theorem compile_run (program : List Mov.Instruction) (source : Mov.State) (target : State)
    (rep : Coherent source target ⟨0, by decide⟩) :
    match Mov.run program source with
    | none => run (compile program) target = none
    | some next => ∃ finish, run (compile program) target = some finish ∧ Coherent next finish ⟨0, by decide⟩ := by
  induction program generalizing source target with
  | nil => exact ⟨target, rfl, rep⟩
  | cons i rest ih =>
    cases first : Mov.execute i source with
    | none =>
      simp only [Mov.run, first, Option.bind_none]
      have stopped := compile_instruction_fault i source target rep first
      simpa only [compile, List.flatMap_cons] using run_after_failure (compileInstruction i) (compile rest) target stopped
    | some middle =>
      rcases compile_instruction_correct i source middle target rep first with ⟨physical, completed, represented⟩
      have tail := ih middle physical represented
      cases restRun : Mov.run rest middle with
      | none =>
        simp only [restRun] at tail
        simp only [Mov.run, first, Option.bind_some, restRun]
        simpa only [compile, List.flatMap_cons] using run_completed_failure completed tail
      | some next =>
        simp only [restRun] at tail
        rcases tail with ⟨finish, tailRun, finishRep⟩
        simp only [Mov.run, first, Option.bind_some, restRun]
        refine ⟨finish, ?_, finishRep⟩
        simpa only [compile, List.flatMap_cons] using run_composition completed tailRun

theorem compile_success (program : List Mov.Instruction) (source next : Mov.State) (target : State)
    (rep : Coherent source target ⟨0, by decide⟩) (h : Mov.run program source = some next) :
    ∃ finish, run (compile program) target = some finish ∧ Coherent next finish ⟨0, by decide⟩ := by
  have correct := compile_run program source target rep
  simpa [h] using correct

theorem compile_fault_iff (program : List Mov.Instruction) (source : Mov.State) (target : State)
    (rep : Coherent source target ⟨0, by decide⟩) :
    run (compile program) target = none ↔ Mov.run program source = none := by
  cases sourceRun : Mov.run program source with
  | none =>
    have correct := compile_run program source target rep
    simpa [sourceRun] using correct
  | some next =>
    rcases compile_success program source next target rep sourceRun with ⟨finish, completed, _⟩
    simp [completed]

end SmcTuring.Dolan.Four

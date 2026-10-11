module
public import SmcTuring.Dolan.Matcher
public import SmcTuring.Dolan.Guard
public import SmcTuring.Dolan.WriteValue
public import SmcTuring.Dolan.AdvanceEffect

public section

namespace SmcTuring.Dolan.Mov

open Encoding Table

@[expose] def CoreRep (s : State) : Prop :=
  s.registers .scratch = .address 0 ∧ s.registers .zero = .offset false ∧
    s.registers .one = .offset true

@[expose] def RuntimeRep {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (s : State) : Prop :=
  CoreRep s ∧ TapeRep (tapeLayout alphabet states) c s ∧ TableRep machine s.memory

theorem core_frame (program : List Instruction) (s finish : State)
    (completed : run program s = some finish) (core : CoreRep s)
    (keep : ∀ i ∈ program, keepsRegister .scratch i ∧ keepsRegister .zero i ∧ keepsRegister .one i) :
    CoreRep finish := by
  exact ⟨(run_register_frame program s finish .scratch completed (fun i hi => (keep i hi).1)).trans core.1,
    (run_register_frame program s finish .zero completed (fun i hi => (keep i hi).2.1)).trans core.2.1,
    (run_register_frame program s finish .one completed (fun i hi => (keep i hi).2.2)).trans core.2.2⟩

theorem runtime_change_state {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (s : State) (q : Fin states)
    (h : RuntimeRep machine c s) : RuntimeRep machine { c with state := q } s := h

theorem guard_runtime {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (s : State) (cursor : Nat)
    (rep : RuntimeRep machine c s) (ht : s.registers .transition = .address cursor)
    (positive : cursor ≠ 0) :
    ∃ finish, run guardProgram s = some finish ∧ RuntimeRep machine c finish ∧
      finish.registers .transition = .address cursor := by
  let finish := guardResult s 0
  have completed := guard_candidate_correct s 0 cursor rep.1.1 ht rep.1.2.1 rep.1.2.2 positive
  have core : CoreRep finish := core_frame guardProgram s finish completed rep.1
    (by simp [guardProgram, keepsRegister])
  have tape : TapeRep (tapeLayout alphabet states) c finish := by
    constructor
    · simpa [RegistersRep, finish, guardResult, write] using rep.2.1.1
    · exact scratch_preserves_memory (tapeLayout alphabet states) c s.memory _ _ rep.2.1.2
  have table : TableRep machine finish.memory := by
    apply table_rep_frame machine s.memory finish.memory rep.2.2
    intro p lower _
    exact guard_memory_frame s 0 p (by omega)
  have cursorKept := run_register_frame guardProgram s finish .transition completed
    (by simp [guardProgram, keepsRegister])
  exact ⟨finish, completed, ⟨core, tape, table⟩, cursorKept.trans ht⟩

theorem match_runtime {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Fin (entries machine c.state).length) (s : State)
    (rep : RuntimeRep machine c s)
    (ht : s.registers .transition = .address (node alphabet c.state index.val)) :
    ∃ finish, run matchCandidateProgram s = some finish ∧ RuntimeRep machine c finish ∧
      finish.registers .transition = .address (node alphabet c.state index.val) ∧
      finish.registers .matched = .offset
        (decide ((entries machine c.state)[index.val].trigger = c.tape c.head)) := by
  rcases match_candidate_correct machine c index s rep.2.2 rep.2.1 ht rep.1.2.1 with
    ⟨finish, completed, matched, tape, table, zero, one⟩
  have scratch := run_register_frame matchCandidateProgram s finish .scratch completed
    (by simp [matchCandidateProgram, loadCandidateProgram, comparison, keepsRegister])
  have cursorKept := run_register_frame matchCandidateProgram s finish .transition completed
    (by simp [matchCandidateProgram, loadCandidateProgram, comparison, keepsRegister])
  exact ⟨finish, completed, ⟨⟨scratch.trans rep.1.1, zero, one⟩, tape, table⟩,
    cursorKept.trans ht, matched⟩

theorem symbol_runtime {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Fin (entries machine c.state).length) (s : State)
    (matched : Bool) (rep : RuntimeRep machine c s)
    (ht : s.registers .transition = .address (node alphabet c.state index.val))
    (hm : s.registers .matched = .offset matched) :
    ∃ finish, run loadSymbolProgram s = some finish ∧ RuntimeRep machine c finish ∧
      finish.registers .transition = .address (node alphabet c.state index.val) ∧
      finish.registers .matched = .offset matched ∧
      finish.registers .y = .address ((entries machine c.state)[index.val].symbol.val + 1) := by
  let finish := symbolInput s ((entries machine c.state)[index.val].symbol.val + 1)
  have completed := load_symbol_correct machine c.state index s rep.2.2 ht rep.1.2.1 rep.1.2.2
  refine ⟨finish, completed, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, rep.2.2⟩
    · simpa [CoreRep, finish, symbolInput, write] using rep.1
    · constructor
      · simpa [RegistersRep, finish, symbolInput, write] using rep.2.1.1
      · exact rep.2.1.2
  · simp [finish, symbolInput, write, ht]
  · simp [finish, symbolInput, write, hm]
  · simp [finish, symbolInput, write]

theorem write_runtime {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (s : State) (symbol : Fin alphabet) (matched : Bool)
    (cursor : Nat) (rep : RuntimeRep machine c s)
    (ht : s.registers .transition = .address cursor)
    (hm : s.registers .matched = .offset matched)
    (hy : s.registers .y = .address (symbol.val + 1)) :
    ∃ finish, run writeValueProgram s = some finish ∧
      RuntimeRep machine (if matched then written c symbol else c) finish ∧
      finish.registers .transition = .address cursor ∧ finish.registers .matched = .offset matched := by
  let layout := tapeLayout alphabet states
  let finish := writeResult s 0 (layout.cell c.head) (.address (symbol.val + 1)) matched
  have completed := write_value_correct s 0 (layout.cell c.head) (.address (symbol.val + 1)) matched
    rep.1.1 rep.2.1.1.1 rep.1.2.1 rep.1.2.2 hm hy
  have core : CoreRep finish := core_frame writeValueProgram s finish completed rep.1
    (by simp [writeValueProgram, selection, keepsRegister])
  have tape : TapeRep layout (if matched then written c symbol else c) finish :=
    symbol_result_represents layout c s symbol matched rep.2.1
  have table : TableRep machine finish.memory := by
    apply table_rep_frame machine s.memory finish.memory rep.2.2
    intro p lower upper
    have above : tableLimit alphabet states ≤ layout.cell c.head := tape_above_table alphabet states c.head
    have different : p ≠ (layout.cell c.head, false) := by
      intro equal
      have := congrArg Prod.fst equal
      omega
    exact write_result_frame s 0 (layout.cell c.head) _ matched p (by omega) different
  have cursorKept := run_register_frame writeValueProgram s finish .transition completed
    (by simp [writeValueProgram, selection, keepsRegister])
  have matchKept := run_register_frame writeValueProgram s finish .matched completed
    (by simp [writeValueProgram, selection, keepsRegister])
  exact ⟨finish, completed, ⟨core, tape, table⟩, cursorKept.trans ht, matchKept.trans hm⟩

theorem direction_runtime {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (index : Fin (entries machine state).length)
    (c : TM.Configuration alphabet states) (s : State) (matched : Bool)
    (rep : RuntimeRep machine c s) (ht : s.registers .transition = .address (node alphabet state index.val))
    (hm : s.registers .matched = .offset matched) :
    ∃ finish, run loadDirectionProgram s = some finish ∧ RuntimeRep machine c finish ∧
      finish.registers .transition = .address (node alphabet state index.val) ∧
      finish.registers .matched = .offset matched ∧
      finish.registers .direction = .offset (entries machine state)[index.val].direction := by
  let finish := directionInput s (entries machine state)[index.val].direction
  have completed := load_direction_correct machine state index s rep.2.2 ht rep.1.2.1 rep.1.2.2
  refine ⟨finish, completed, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, rep.2.2⟩
    · simpa [CoreRep, finish, directionInput, write] using rep.1
    · constructor
      · simpa [RegistersRep, finish, directionInput, write] using rep.2.1.1
      · exact rep.2.1.2
  · simp [finish, directionInput, write, ht]
  · simp [finish, directionInput, write, hm]
  · simp [finish, directionInput, write]

theorem advance_runtime {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (s : State) (direction matched : Bool) (cursor : Nat)
    (rep : RuntimeRep machine c s) (ht : s.registers .transition = .address cursor)
    (hm : s.registers .matched = .offset matched) (hd : s.registers .direction = .offset direction) :
    ∃ finish, run advanceProgram s = some finish ∧
      RuntimeRep machine (if matched then moved c direction else c) finish ∧
      finish.registers .transition = .address cursor ∧ finish.registers .matched = .offset matched := by
  let layout := tapeLayout alphabet states
  rcases advance_program_correct layout c s direction matched rep.2.1
    rep.1.1 rep.1.2.1 rep.1.2.2 hd hm with ⟨finish, completed, tape⟩
  have exactRun := advance_exact s 0 (layout.cell c.head) (layout.cell (c.head - 1))
    (layout.cell (c.head + 1)) direction matched rep.1.1 rep.2.1.1.1 rep.2.1.1.2.1 rep.2.1.1.2.2
    rep.1.2.1 rep.1.2.2 hd hm (layout.cell_scratch _) (layout.cell_scratch _) (layout.cell_scratch _)
  have equal : finish = advanceResult s 0 (layout.cell c.head) (layout.cell (c.head - 1))
      (layout.cell (c.head + 1)) direction matched := Option.some.inj (completed.symm.trans exactRun)
  have table : TableRep machine finish.memory := by
    apply table_rep_frame machine s.memory finish.memory rep.2.2
    intro p lower upper
    have above : tableLimit alphabet states ≤ layout.cell c.head := tape_above_table alphabet states c.head
    have different : p ≠ (layout.cell c.head, true) := by
      intro same
      have := congrArg Prod.fst same
      omega
    rw [equal]
    exact advance_result_frame s 0 _ _ _ direction matched p (by omega) different
  have core := core_frame advanceProgram s finish completed rep.1
    (by simp [advanceProgram, pushProgram, popDirectionProgram, popProgram, keepsRegister])
  have cursorKept := run_register_frame advanceProgram s finish .transition completed
    (by simp [advanceProgram, pushProgram, popDirectionProgram, popProgram, keepsRegister])
  have matchKept := run_register_frame advanceProgram s finish .matched completed
    (by simp [advanceProgram, pushProgram, popDirectionProgram, popProgram, keepsRegister])
  exact ⟨finish, completed, ⟨core, tape, table⟩, cursorKept.trans ht, matchKept.trans hm⟩

theorem cursor_runtime {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (state : Fin states) (index : Fin (entries machine state).length)
    (c : TM.Configuration alphabet states) (s : State) (matched : Bool)
    (rep : RuntimeRep machine c s) (ht : s.registers .transition = .address (node alphabet state index.val))
    (hm : s.registers .matched = .offset matched) :
    ∃ finish, run updateCursorProgram s = some finish ∧ RuntimeRep machine c finish ∧
      finish.registers .transition = .address
        (if matched then head machine (entries machine state)[index.val].destination
         else cursor machine state (index.val + 1)) := by
  let prepared := candidateInput s (cursor machine state (index.val + 1))
    (head machine (entries machine state)[index.val].destination)
  let finish := cursorSelectionResult prepared 0 matched
  have loaded : run loadCursorChoicesProgram s = some prepared :=
    load_cursor_choices_correct machine state index s rep.2.2 ht rep.1.2.1 rep.1.2.2
  have pn : prepared.registers .scratch = .address 0 := by simp [prepared, candidateInput, write, rep.1.1]
  have p0 : prepared.registers .zero = .offset false := by simp [prepared, candidateInput, write, rep.1.2.1]
  have p1 : prepared.registers .one = .offset true := by simp [prepared, candidateInput, write, rep.1.2.2]
  have pm : prepared.registers .matched = .offset matched := by simp [prepared, candidateInput, write, hm]
  have completed : run updateCursorProgram s = some finish :=
    run_composition loaded (cursor_selection_correct prepared 0 matched pn p0 p1 pm)
  have core := core_frame updateCursorProgram s finish completed rep.1
    (by simp [updateCursorProgram, loadCursorChoicesProgram, cursorSelectionProgram, keepsRegister])
  have tape : TapeRep (tapeLayout alphabet states) c finish := by
    constructor
    · simpa [RegistersRep, finish, cursorSelectionResult, prepared, candidateInput, write] using rep.2.1.1
    · exact scratch_preserves_memory (tapeLayout alphabet states) c s.memory _ _ rep.2.1.2
  have table : TableRep machine finish.memory := by
    apply table_rep_frame machine s.memory finish.memory rep.2.2
    intro p lower _
    have ne : p.1 ≠ 0 := by omega
    rcases p with ⟨cell, choice⟩
    cases choice <;> simp_all [finish, cursorSelectionResult, prepared, candidateInput, write]
  refine ⟨finish, completed, ⟨core, tape, table⟩, ?_⟩
  cases matched <;> simp [finish, cursorSelectionResult, prepared, candidateInput, write]

end SmcTuring.Dolan.Mov

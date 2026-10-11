module
public import SmcTuring.Dolan.TablePrograms

public section

namespace SmcTuring.Dolan.Mov

open Encoding Table

@[expose] def matchCandidateProgram : List Instruction := loadCandidateProgram ++ comparison

theorem symbol_address_equality {alphabet : Nat} (a b : Fin alphabet) :
    a.val + 1 = b.val + 1 ↔ a = b := by
  constructor
  · intro h
    apply Fin.ext
    omega
  · intro h
    rw [h]

/-- The matching flag is computed by eight literal MOVs from the table and
the current tape payload. No matching predicate is assumed as an instruction. -/
theorem match_candidate_correct {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Fin (entries machine c.state).length) (s : State)
    (table : TableRep machine s.memory) (tape : TapeRep (tapeLayout alphabet states) c s)
    (ht : s.registers .transition = .address (node alphabet c.state index.val))
    (h0 : s.registers .zero = .offset false) :
    ∃ finish, run matchCandidateProgram s = some finish ∧
      finish.registers .matched = .offset
        (decide ((entries machine c.state)[index.val].trigger = c.tape c.head)) ∧
      TapeRep (tapeLayout alphabet states) c finish ∧ TableRep machine finish.memory ∧
      finish.registers .zero = .offset false ∧ finish.registers .one = .offset true := by
  let trigger := (entries machine c.state)[index.val].trigger
  let symbol := c.tape c.head
  let prepared := candidateInput s (trigger.val + 1) (symbol.val + 1)
  let finish := comparisonResult prepared (trigger.val + 1) (symbol.val + 1)
  have loaded : run loadCandidateProgram s = some prepared :=
    load_candidate_correct machine c index s table tape ht h0
  have px : prepared.registers .x = .address (trigger.val + 1) := by
    simp [prepared, candidateInput, write]
  have py : prepared.registers .y = .address (symbol.val + 1) := by
    simp [prepared, candidateInput, write]
  have compared : run comparison prepared = some finish :=
    comparison_correct prepared (trigger.val + 1) (symbol.val + 1) px py
  have runAll : run matchCandidateProgram s = some finish := run_composition loaded compared
  have matched : finish.registers .matched = .offset (decide (trigger = symbol)) := by
    simp [finish, comparisonResult, write]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have represented : TapeRep (tapeLayout alphabet states) c finish := by
    rcases tape with ⟨⟨current, left, right⟩, ⟨payload, leftLink, rightLink⟩⟩
    constructor
    · simp [RegistersRep, finish, comparisonResult, prepared, candidateInput, write,
        current, left, right]
    · refine ⟨?_, ?_, ?_⟩
      · intro position
        have above := tape_above_table alphabet states position
        have tx := trigger.isLt
        have sy := symbol.isLt
        have hx : (tapeLayout alphabet states).cell position ≠ trigger.val + 1 := by
          simp only [tableLimit] at above
          omega
        have hy : (tapeLayout alphabet states).cell position ≠ symbol.val + 1 := by
          simp only [tableLimit] at above
          omega
        simpa [finish, comparisonResult, prepared, candidateInput, write, hx, hy] using payload position
      · intro position hp
        simpa [finish, comparisonResult, prepared, candidateInput, write] using leftLink position hp
      · intro position hp
        simpa [finish, comparisonResult, prepared, candidateInput, write] using rightLink position hp
  have preserved : TableRep machine finish.memory := by
    apply table_rep_frame machine s.memory finish.memory table
    intro p lower upper
    have tx := trigger.isLt
    have sy := symbol.isLt
    have hx : p.1 ≠ trigger.val + 1 := by omega
    have hy : p.1 ≠ symbol.val + 1 := by omega
    rcases p with ⟨cell, choice⟩
    cases choice <;> simp_all [finish, comparisonResult, prepared, candidateInput, write]
  have zero : finish.registers .zero = .offset false := by
    simp [finish, comparisonResult, write]
  have one : finish.registers .one = .offset true := by simp [finish, comparisonResult, write]
  exact ⟨finish, runAll, matched, represented, preserved, zero, one⟩

end SmcTuring.Dolan.Mov

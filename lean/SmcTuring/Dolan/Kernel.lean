module
public import SmcTuring.Dolan.KernelState

public section

namespace SmcTuring.Dolan.Mov

open Encoding Table

/-- One fixed, machine-independent body. Machine information is read from
the linked transition table. Repetition supplies one unconditional backedge. -/
@[expose] def kernelProgram : List Instruction :=
  guardProgram ++ (matchCandidateProgram ++ (loadSymbolProgram ++
    (writeValueProgram ++ (loadDirectionProgram ++ (advanceProgram ++ updateCursorProgram)))))

theorem kernel_length : kernelProgram.length = 64 := by decide

@[expose] def applyEntry {alphabet states : Nat} (c : TM.Configuration alphabet states)
    (entry : Entry alphabet states) : TM.Configuration alphabet states :=
  { state := entry.destination
    head := if entry.direction then c.head + 1 else c.head - 1
    tape := write c.tape c.head entry.symbol }

/-- A complete body either performs the selected transition or preserves the
logical configuration and advances to the next candidate. Its match flag is
computed by literal MOVs; all memory and cursor effects are included. -/
theorem kernel_candidate_correct {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (index : Fin (entries machine c.state).length) (s : State)
    (rep : RuntimeRep machine c s)
    (ht : s.registers .transition = .address (node alphabet c.state index.val)) :
    let entry := (entries machine c.state)[index.val]
    let matched := decide (entry.trigger = c.tape c.head)
    ∃ finish, run kernelProgram s = some finish ∧
      RuntimeRep machine (if matched then applyEntry c entry else c) finish ∧
      finish.registers .transition = .address
        (if matched then head machine entry.destination else cursor machine c.state (index.val + 1)) := by
  let entry := (entries machine c.state)[index.val]
  let matched := decide (entry.trigger = c.tape c.head)
  have positive : node alphabet c.state index.val ≠ 0 := by simp only [node]; omega
  rcases guard_runtime machine c s _ rep ht positive with ⟨guarded, hg, rg, tg⟩
  rcases match_runtime machine c index guarded rg tg with ⟨compared, hc, rc, tc, mc⟩
  rcases symbol_runtime machine c index compared matched rc tc mc with ⟨loaded, hl, rl, tl, ml, yl⟩
  rcases write_runtime machine c loaded entry.symbol matched _ rl tl ml yl with
    ⟨writtenState, hw, rw, tw, mw⟩
  let writtenConfig := if matched then written c entry.symbol else c
  rcases direction_runtime machine c.state index writtenConfig writtenState matched rw tw mw with
    ⟨directed, hd, rd, td, md, dd⟩
  rcases advance_runtime machine writtenConfig directed entry.direction matched _ rd td md dd with
    ⟨advanced, ha, ra, ta, ma⟩
  let advancedConfig := if matched then moved writtenConfig entry.direction else writtenConfig
  rcases cursor_runtime machine c.state index advancedConfig advanced matched ra ta ma with
    ⟨finish, hu, ru, tu⟩
  have completed : run kernelProgram s = some finish :=
    run_composition hg (run_composition hc (run_composition hl (run_composition hw
      (run_composition hd (run_composition ha hu)))))
  have represented : RuntimeRep machine (if matched then applyEntry c entry else c) finish := by
    cases h : matched
    · simpa [advancedConfig, writtenConfig, h] using ru
    · have changed := runtime_change_state machine advancedConfig finish entry.destination ru
      simpa [advancedConfig, writtenConfig, h, moved, written, applyEntry] using changed
  exact ⟨finish, completed, represented, tu⟩

theorem kernel_sentinel_traps {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (s : State) (rep : RuntimeRep machine c s)
    (ht : s.registers .transition = .address 0) : run kernelProgram s = none := by
  have stopped := guard_sentinel_traps s 0 rep.1.1 ht rep.1.2.1 rep.1.2.2
  rw [kernelProgram, run_append, stopped]
  rfl

end SmcTuring.Dolan.Mov

module
public import SmcTuring.Dolan.Advance

public section

namespace SmcTuring.Dolan.Encoding

open Mov

/-- The selected symbol-write effect preserves the tape representation. -/
theorem symbol_result_represents {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (s : State) (symbol : Fin alphabet) (matched : Bool)
    (h : TapeRep layout c s) :
    TapeRep layout (if matched then written c symbol else c)
      (writeResult s layout.scratch (layout.cell c.head) (.address (layout.symbol symbol)) matched) := by
  rcases h with ⟨registers, memory⟩
  constructor
  · rcases registers with ⟨hs, hl, hr⟩
    cases matched <;> simp [RegistersRep, written, writeResult, write, hs, hl, hr]
  · rcases memory with ⟨payload, left, right⟩
    refine ⟨?_, ?_, ?_⟩
    · intro position
      by_cases hp : position = c.head
      · subst position
        cases matched <;> simp [written, writeResult, write, payload c.head]
      · have hc : layout.cell position ≠ layout.cell c.head :=
          fun equal => hp (layout.cell_injective equal)
        cases matched <;>
          simpa [written, writeResult, write, hp, hc, layout.cell_scratch] using payload position
    · intro position hp
      have old : position < c.head := by cases matched <;> simpa [written] using hp
      cases matched <;>
        simpa [written, writeResult, write, layout.cell_scratch] using left position old
    · intro position hp
      have old : c.head < position := by cases matched <;> simpa [written] using hp
      cases matched <;>
        simpa [written, writeResult, write, layout.cell_scratch] using right position old

/-- The selected write block preserves the registers needed by the motion block.
Keep its output existential here so the next proof uses an abstract state. -/
theorem selected_write_program_correct {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (s : State) (symbol : Fin alphabet)
    (direction matched : Bool)
    (h : TapeRep layout c s)
    (hn : s.registers .scratch = .address layout.scratch)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hd : s.registers .direction = .offset direction)
    (hm : s.registers .matched = .offset matched) :
    ∃ afterWrite, run (writeProgram (.address (layout.symbol symbol))) s = some afterWrite ∧
      TapeRep layout (if matched then written c symbol else c) afterWrite ∧
      afterWrite.registers .scratch = .address layout.scratch ∧
      afterWrite.registers .zero = .offset false ∧
      afterWrite.registers .one = .offset true ∧
      afterWrite.registers .direction = .offset direction ∧
      afterWrite.registers .matched = .offset matched := by
  let afterWrite := writeResult s layout.scratch (layout.cell c.head)
                                (.address (layout.symbol symbol)) matched
  have hs := h.1.1
  have writeRun : run (writeProgram (.address (layout.symbol symbol))) s = some afterWrite :=
    write_program_correct s layout.scratch (layout.cell c.head) _ matched hn hs h0 h1 hm
  have nextRep : TapeRep layout (if matched then written c symbol else c) afterWrite :=
    symbol_result_represents layout c s symbol matched h
  have wn : afterWrite.registers .scratch = .address layout.scratch := by
    simp [afterWrite, writeResult, write, hn]
  have w0 : afterWrite.registers .zero = .offset false := by simp [afterWrite, writeResult, write, h0]
  have w1 : afterWrite.registers .one = .offset true := by simp [afterWrite, writeResult, write, h1]
  have wd : afterWrite.registers .direction = .offset direction := by
    simp [afterWrite, writeResult, write, hd]
  have wm : afterWrite.registers .matched = .offset matched := by
    simp [afterWrite, writeResult, write, hm]
  exact ⟨afterWrite, writeRun, nextRep, wn, w0, w1, wd, wm⟩

/-- Thirty-two literal MOV instructions perform the tape part of a selected
TM transition. The state update and transition-table matcher are separate. -/
theorem tape_step_program_correct {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (s : State) (symbol : Fin alphabet)
    (direction matched : Bool)
    (h : TapeRep layout c s)
    (hn : s.registers .scratch = .address layout.scratch)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hd : s.registers .direction = .offset direction)
    (hm : s.registers .matched = .offset matched) :
    ∃ finish, run (writeProgram (.address (layout.symbol symbol)) ++ advanceProgram) s = some finish ∧
      TapeRep layout (if matched then moved (written c symbol) direction else c) finish := by
  cases matched with
  | false =>
    rcases selected_write_program_correct layout c s symbol direction false h hn h0 h1 hd hm with
      ⟨afterWrite, writeRun, nextRep, wn, w0, w1, wd, wm⟩
    rcases advance_program_correct layout c afterWrite direction false nextRep wn w0 w1 wd wm with
      ⟨finish, advanceRun, represented⟩
    exact ⟨finish, run_composition writeRun advanceRun, represented⟩
  | true =>
    rcases selected_write_program_correct layout c s symbol direction true h hn h0 h1 hd hm with
      ⟨afterWrite, writeRun, nextRep, wn, w0, w1, wd, wm⟩
    rcases advance_program_correct layout (written c symbol) afterWrite direction true
      nextRep wn w0 w1 wd wm with ⟨finish, advanceRun, represented⟩
    exact ⟨finish, run_composition writeRun advanceRun, represented⟩

end SmcTuring.Dolan.Encoding

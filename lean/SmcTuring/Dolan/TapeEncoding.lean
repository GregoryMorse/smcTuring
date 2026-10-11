module
public import SmcTuring.Turing
public import SmcTuring.Dolan.TapePrograms

public section

namespace SmcTuring.Dolan.Encoding

open Mov

/-- Distinct logical tape positions have distinct physical cells. The scratch
cell is separate. Symbols are represented by addresses, as in Dolan's paper. -/
structure Layout (alphabet : Nat) where
  cell : Int → Nat
  symbol : Fin alphabet → Nat
  scratch : Nat
  cell_injective : Function.Injective cell
  cell_scratch : ∀ position, cell position ≠ scratch

/-- The link in the current cell is deliberately unconstrained. All other
links point away from the head, implementing the two persistent stacks. -/
@[expose] def MemoryRep {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (memory : Memory) : Prop :=
  (∀ position, memory (layout.cell position, false) = .address (layout.symbol (c.tape position))) ∧
  (∀ position, position < c.head →
    memory (layout.cell position, true) = .address (layout.cell (position - 1))) ∧
  (∀ position, c.head < position →
    memory (layout.cell position, true) = .address (layout.cell (position + 1)))

@[expose] def RegistersRep {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (registers : Register → Word) : Prop :=
  registers .current = .address (layout.cell c.head) ∧
  registers .left = .address (layout.cell (c.head - 1)) ∧
  registers .right = .address (layout.cell (c.head + 1))

@[expose] def TapeRep {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (s : State) : Prop :=
  RegistersRep layout c s.registers ∧ MemoryRep layout c s.memory

@[expose] def written {alphabet states : Nat} (c : TM.Configuration alphabet states)
    (symbol : Fin alphabet) : TM.Configuration alphabet states :=
  { c with tape := write c.tape c.head symbol }

@[expose] def moved {alphabet states : Nat} (c : TM.Configuration alphabet states)
    (right : Bool) : TM.Configuration alphabet states :=
  { c with head := if right then c.head + 1 else c.head - 1 }

/-- Writing the current tape symbol preserves every stack link. -/
theorem write_preserves_memory {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (memory : Memory) (symbol : Fin alphabet)
    (h : MemoryRep layout c memory) :
    MemoryRep layout (written c symbol)
      (write memory (layout.cell c.head, false) (.address (layout.symbol symbol))) := by
  rcases h with ⟨payload, left, right⟩
  refine ⟨?_, ?_, ?_⟩
  · intro position
    by_cases hp : position = c.head
    · subst position
      simp [written, write]
    · have hc : layout.cell position ≠ layout.cell c.head :=
        fun equal => hp (layout.cell_injective equal)
      simpa [written, write, hp, hc] using payload position
  · intro position hp
    simpa [written, write] using left position hp
  · intro position hp
    simpa [written, write] using right position hp

/-- A head move changes only the former current cell's link. The invariant
constrains that link after the cell becomes part of a stack. -/
theorem move_preserves_memory {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (memory : Memory) (right : Bool)
    (h : MemoryRep layout c memory) :
    MemoryRep layout (moved c right)
      (write memory (layout.cell c.head, true)
        (.address (layout.cell (if right then c.head - 1 else c.head + 1)))) := by
  rcases h with ⟨payload, left, rightLink⟩
  refine ⟨?_, ?_, ?_⟩
  · intro position
    simpa [moved, write] using payload position
  · intro position hp
    by_cases he : position = c.head
    · subst position
      cases right <;> simp_all [moved, write] <;> omega
    · have hc : layout.cell position ≠ layout.cell c.head :=
        fun equal => he (layout.cell_injective equal)
      have old : position < c.head := by cases right <;> simp_all [moved] <;> omega
      simpa [write, hc] using left position old
  · intro position hp
    by_cases he : position = c.head
    · subst position
      cases right <;> simp_all [moved, write] <;> omega
    · have hc : layout.cell position ≠ layout.cell c.head :=
        fun equal => he (layout.cell_injective equal)
      have old : c.head < position := by cases right <;> simp_all [moved] <;> omega
      simpa [write, hc] using rightLink position old

/-- The selector workspace cannot corrupt a represented tape. -/
theorem scratch_preserves_memory {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (memory : Memory) (first second : Word)
    (h : MemoryRep layout c memory) :
    MemoryRep layout c (write (write memory (layout.scratch, false) first)
                             (layout.scratch, true) second) := by
  rcases h with ⟨payload, left, right⟩
  refine ⟨?_, ?_, ?_⟩
  · intro position
    simpa [write, layout.cell_scratch position] using payload position
  · intro position hp
    simpa [write, layout.cell_scratch position] using left position hp
  · intro position hp
    simpa [write, layout.cell_scratch position] using right position hp

/-- The chosen left or right neighbor's old link is available from the invariant. -/
theorem neighbor_link {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (memory : Memory) (right : Bool)
    (h : MemoryRep layout c memory) :
    memory (layout.cell (if right then c.head + 1 else c.head - 1), true) =
      .address (layout.cell (if right then c.head + 2 else c.head - 2)) := by
  rcases h with ⟨_, left, rightLink⟩
  cases right
  · have hh : c.head - 1 < c.head := by omega
    simpa [show c.head - 1 - 1 = c.head - 2 by omega] using left (c.head - 1) hh
  · have hh : c.head < c.head + 1 := by omega
    simpa [show c.head + 1 + 1 = c.head + 2 by omega] using rightLink (c.head + 1) hh

/-- Execution of twenty actual MOV instructions realizes one tape head move.
This theorem does not treat tape motion as a primitive instruction. -/
theorem move_program_correct {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (s : State) (right : Bool)
    (h : TapeRep layout c s)
    (hn : s.registers .scratch = .address layout.scratch)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hd : s.registers .direction = .offset right) :
    ∃ finish, run (pushProgram ++ popProgram) s = some finish ∧
      TapeRep layout (moved c right) finish := by
  rcases h with ⟨⟨hs, hl, hr⟩, memoryRep⟩
  let middle := pushResult s layout.scratch (layout.cell c.head) right
  let left := layout.cell (if right then c.head else c.head - 1)
  let rightCell := layout.cell (if right then c.head + 1 else c.head)
  let finish := popResult middle layout.scratch left rightCell right
  have pushRun : run pushProgram s = some middle :=
    push_program_correct s layout.scratch (layout.cell c.head) right hn hs h0 h1 hd
      (layout.cell_scratch c.head)
  have ml : middle.registers .left = .address left := by
    cases right <;> simp [middle, left, pushResult, write, hl]
  have mr : middle.registers .right = .address rightCell := by
    cases right <;> simp [middle, rightCell, pushResult, write, hr]
  have mn : middle.registers .scratch = .address layout.scratch := by
    simp [middle, pushResult, write, hn]
  have m0 : middle.registers .zero = .offset false := by simp [middle, pushResult, write, h0]
  have m1 : middle.registers .one = .offset true := by simp [middle, pushResult, write, h1]
  have md : middle.registers .direction = .offset right := by simp [middle, pushResult, write, hd]
  have ld : left ≠ layout.scratch := layout.cell_scratch _
  have rd : rightCell ≠ layout.scratch := layout.cell_scratch _
  have popRun : run popProgram middle = some finish :=
    pop_program_correct middle layout.scratch left rightCell right mn ml mr m0 m1 md ld rd
  refine ⟨finish, ?_, ?_⟩
  · rw [run_append, pushRun]
    exact popRun
  · have movedMemory : MemoryRep layout (moved c right) middle.memory := by
      have hm := move_preserves_memory layout c s.memory right memoryRep
      have hscratch := scratch_preserves_memory layout (moved c right) _
        (.address (layout.cell c.head)) (s.registers .right) hm
      cases right <;>
        simpa [middle, pushResult, hl, hr] using hscratch
    constructor
    · have hleft : layout.cell (c.head - 1) ≠ layout.cell c.head := by
        intro he
        have := layout.cell_injective he
        omega
      have hright : layout.cell (c.head + 1) ≠ layout.cell c.head := by
        intro he
        have := layout.cell_injective he
        omega
      have tailLeft : s.memory (layout.cell (c.head - 1), true) =
          .address (layout.cell (c.head - 2)) := by
        simpa using neighbor_link layout c s.memory false memoryRep
      have tailRight : s.memory (layout.cell (c.head + 1), true) =
          .address (layout.cell (c.head + 2)) := by
        simpa using neighbor_link layout c s.memory true memoryRep
      cases right <;>
        simp_all [RegistersRep, moved, finish, popResult, middle, pushResult, left, rightCell,
          write, layout.cell_scratch,
          show c.head - 1 - 1 = c.head - 2 by omega,
          show c.head + 1 + 1 = c.head + 2 by omega]
    · exact scratch_preserves_memory layout (moved c right) middle.memory _ _ movedMemory

end SmcTuring.Dolan.Encoding

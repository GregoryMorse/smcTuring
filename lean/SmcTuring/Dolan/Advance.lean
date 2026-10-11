module
public import SmcTuring.Dolan.Initialization

public section

namespace SmcTuring.Dolan.Encoding

open Mov

/-- An unmatched block may overwrite the unused current link without changing
the tape represented by that memory. -/
theorem current_link_preserves_memory {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (memory : Memory) (value : Word)
    (h : MemoryRep layout c memory) :
    MemoryRep layout c (write memory (layout.cell c.head, true) value) := by
  rcases h with ⟨payload, left, right⟩
  refine ⟨?_, ?_, ?_⟩
  · intro position
    simpa [write] using payload position
  · intro position hp
    have hc : layout.cell position ≠ layout.cell c.head := by
      intro equal
      have := layout.cell_injective equal
      omega
    simpa [write, hc] using left position hp
  · intro position hp
    have hc : layout.cell position ≠ layout.cell c.head := by
      intro equal
      have := layout.cell_injective equal
      omega
    simpa [write, hc] using right position hp

/-- The paper's conditional motion is a 26-instruction MOV program. On a
match it moves once; on a nonmatch it preserves the represented configuration,
including tape contents. No conditional branch is used. -/
theorem advance_program_correct {alphabet states : Nat} (layout : Layout alphabet)
    (c : TM.Configuration alphabet states) (s : State) (direction matched : Bool)
    (h : TapeRep layout c s)
    (hn : s.registers .scratch = .address layout.scratch)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hd : s.registers .direction = .offset direction)
    (hm : s.registers .matched = .offset matched) :
    ∃ finish, run advanceProgram s = some finish ∧
      TapeRep layout (if matched then moved c direction else c) finish := by
  rcases h with ⟨⟨hs, hl, hr⟩, memoryRep⟩
  let pushed := pushResult s layout.scratch (layout.cell c.head) direction
  let flipped := popDirectionResult pushed layout.scratch direction matched
  let left := layout.cell (if direction then c.head else c.head - 1)
  let right := layout.cell (if direction then c.head + 1 else c.head)
  let finish := popResult flipped layout.scratch left right
                          (if matched then direction else !direction)
  have pushRun : run pushProgram s = some pushed :=
    push_program_correct s layout.scratch (layout.cell c.head) direction hn hs h0 h1 hd
      (layout.cell_scratch c.head)
  have pn : pushed.registers .scratch = .address layout.scratch := by
    simp [pushed, pushResult, write, hn]
  have p0 : pushed.registers .zero = .offset false := by simp [pushed, pushResult, write, h0]
  have p1 : pushed.registers .one = .offset true := by simp [pushed, pushResult, write, h1]
  have pd : pushed.registers .direction = .offset direction := by simp [pushed, pushResult, write, hd]
  have pm : pushed.registers .matched = .offset matched := by simp [pushed, pushResult, write, hm]
  have flipRun : run popDirectionProgram pushed = some flipped :=
    pop_direction_program_correct pushed layout.scratch direction matched pn p0 p1 pd pm
  have fn : flipped.registers .scratch = .address layout.scratch := by
    simp [flipped, popDirectionResult, write, pn]
  have f0 : flipped.registers .zero = .offset false := by simp [flipped, popDirectionResult, write, p0]
  have f1 : flipped.registers .one = .offset true := by simp [flipped, popDirectionResult, write, p1]
  have fd : flipped.registers .direction =
      .offset (if matched then direction else !direction) := by
    simp [flipped, popDirectionResult, write]
  have fl : flipped.registers .left = .address left := by
    cases direction <;> simp [flipped, popDirectionResult, pushed, pushResult, left, write, hl]
  have fr : flipped.registers .right = .address right := by
    cases direction <;> simp [flipped, popDirectionResult, pushed, pushResult, right, write, hr]
  have popRun : run popProgram flipped = some finish :=
    pop_program_correct flipped layout.scratch left right (if matched then direction else !direction)
      fn fl fr f0 f1 fd (layout.cell_scratch _) (layout.cell_scratch _)
  refine ⟨finish, ?_, ?_⟩
  · simp only [advanceProgram, run_append, pushRun, Option.bind_some, flipRun]
    exact popRun
  · let target := if matched then moved c direction else c
    have pushedMemory : MemoryRep layout target pushed.memory := by
      have baseMemory : MemoryRep layout target
          (write s.memory (layout.cell c.head, true)
            (.address (layout.cell (if direction then c.head - 1 else c.head + 1)))) := by
        cases matched
        · exact current_link_preserves_memory layout c s.memory _ memoryRep
        · exact move_preserves_memory layout c s.memory direction memoryRep
      have scratchMemory := scratch_preserves_memory layout target _
        (.address (layout.cell c.head)) (s.registers .right) baseMemory
      cases direction <;> simpa [pushed, pushResult, hl, hr] using scratchMemory
    have flippedMemory : MemoryRep layout target flipped.memory :=
      scratch_preserves_memory layout target pushed.memory _ _ pushedMemory
    constructor
    · have hleft : layout.cell (c.head - 1) ≠ layout.cell c.head := by
        intro equal
        have := layout.cell_injective equal
        omega
      have hright : layout.cell (c.head + 1) ≠ layout.cell c.head := by
        intro equal
        have := layout.cell_injective equal
        omega
      have tailLeft : s.memory (layout.cell (c.head - 1), true) =
          .address (layout.cell (c.head - 2)) := by
        simpa using neighbor_link layout c s.memory false memoryRep
      have tailRight : s.memory (layout.cell (c.head + 1), true) =
          .address (layout.cell (c.head + 2)) := by
        simpa using neighbor_link layout c s.memory true memoryRep
      cases direction <;> cases matched <;>
        simp_all [RegistersRep, target, moved, finish, popResult, flipped, popDirectionResult,
          pushed, pushResult, left, right, write, layout.cell_scratch,
          show c.head - 1 - 1 = c.head - 2 by omega,
          show c.head + 1 + 1 = c.head + 2 by omega]
    · exact scratch_preserves_memory layout target flipped.memory _ _ flippedMemory

end SmcTuring.Dolan.Encoding

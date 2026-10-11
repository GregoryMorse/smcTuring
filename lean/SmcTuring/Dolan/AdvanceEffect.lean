module
public import SmcTuring.Dolan.Advance
public import SmcTuring.Dolan.Frames

public section

namespace SmcTuring.Dolan.Mov

@[expose] def advanceResult (s : State) (scratch current left right : Nat)
    (direction matched : Bool) : State :=
  let pushed := pushResult s scratch current direction
  let flipped := popDirectionResult pushed scratch direction matched
  popResult flipped scratch (if direction then current else left)
    (if direction then right else current) (if matched then direction else !direction)

/-- Exact execution complements the logical tape theorem with the full
memory effect needed to preserve the immutable transition table. -/
theorem advance_exact (s : State) (scratch current left right : Nat) (direction matched : Bool)
    (hn : s.registers .scratch = .address scratch)
    (hs : s.registers .current = .address current)
    (hl : s.registers .left = .address left) (hr : s.registers .right = .address right)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hd : s.registers .direction = .offset direction) (hm : s.registers .matched = .offset matched)
    (ns : current ≠ scratch) (nl : left ≠ scratch) (nr : right ≠ scratch) :
    run advanceProgram s = some (advanceResult s scratch current left right direction matched) := by
  let pushed := pushResult s scratch current direction
  let flipped := popDirectionResult pushed scratch direction matched
  have pushedRun : run pushProgram s = some pushed :=
    push_program_correct s scratch current direction hn hs h0 h1 hd ns
  have pn : pushed.registers .scratch = .address scratch := by simp [pushed, pushResult, write, hn]
  have p0 : pushed.registers .zero = .offset false := by simp [pushed, pushResult, write, h0]
  have p1 : pushed.registers .one = .offset true := by simp [pushed, pushResult, write, h1]
  have pd : pushed.registers .direction = .offset direction := by simp [pushed, pushResult, write, hd]
  have pm : pushed.registers .matched = .offset matched := by simp [pushed, pushResult, write, hm]
  have flippedRun : run popDirectionProgram pushed = some flipped :=
    pop_direction_program_correct pushed scratch direction matched pn p0 p1 pd pm
  have fn : flipped.registers .scratch = .address scratch := by
    simp [flipped, popDirectionResult, write, pn]
  have f0 : flipped.registers .zero = .offset false := by simp [flipped, popDirectionResult, write, p0]
  have f1 : flipped.registers .one = .offset true := by simp [flipped, popDirectionResult, write, p1]
  have fd : flipped.registers .direction = .offset (if matched then direction else !direction) := by
    simp [flipped, popDirectionResult, write]
  have fl : flipped.registers .left = .address (if direction then current else left) := by
    cases direction <;> simp [flipped, popDirectionResult, pushed, pushResult, write, hl]
  have fr : flipped.registers .right = .address (if direction then right else current) := by
    cases direction <;> simp [flipped, popDirectionResult, pushed, pushResult, write, hr]
  have leftSeparate : (if direction then current else left) ≠ scratch := by
    cases direction <;> assumption
  have rightSeparate : (if direction then right else current) ≠ scratch := by
    cases direction <;> assumption
  have poppedRun := pop_program_correct flipped scratch
    (if direction then current else left) (if direction then right else current)
    (if matched then direction else !direction) fn fl fr f0 f1 fd leftSeparate rightSeparate
  exact run_composition (run_composition pushedRun flippedRun) poppedRun

theorem advance_result_frame (s : State) (scratch current left right : Nat) (direction matched : Bool)
    (p : Nat × Bool) (hn : p.1 ≠ scratch) (hs : p ≠ (current, true)) :
    (advanceResult s scratch current left right direction matched).memory p = s.memory p := by
  rcases p with ⟨cell, choice⟩
  cases choice <;>
    simp_all [advanceResult, popResult, popDirectionResult, pushResult, write]

end SmcTuring.Dolan.Mov

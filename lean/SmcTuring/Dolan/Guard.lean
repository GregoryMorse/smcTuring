module
public import SmcTuring.Dolan.Programs
public import SmcTuring.Dolan.Frames

public section

namespace SmcTuring.Dolan.Mov

/-- Guard the sentinel before dereferencing a candidate. The comparison saves
and restores the cursor's first word. A zero result is dereferenced to halt;
a nonzero result selects the valid scratch cell. This is the corrected polarity. -/
@[expose] def guardProgram : List Instruction :=
  [.load .x .transition .zero,
   .store .scratch .zero .one, .store .transition .zero .zero,
   .load .halted .scratch .zero, .store .transition .zero .x,
   .store .scratch .zero .zero, .store .scratch .one .scratch,
   .load .x .scratch .halted, .load .x .x .zero]

@[expose] def guardResult (s : State) (scratch : Nat) : State :=
  { registers := write (write s.registers .halted (.offset true)) .x (.offset false)
    memory := write (write s.memory (scratch, false) (.offset false))
                    (scratch, true) (.address scratch) }

theorem guard_sentinel_traps (s : State) (scratch : Nat)
    (hn : s.registers .scratch = .address scratch)
    (ht : s.registers .transition = .address scratch)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true) :
    run guardProgram s = none := by
  simp [guardProgram, run, execute, address, write, hn, ht, h0, h1]

theorem guard_candidate_correct (s : State) (scratch cursor : Nat)
    (hn : s.registers .scratch = .address scratch)
    (ht : s.registers .transition = .address cursor)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (different : cursor ≠ scratch) :
    run guardProgram s = some (guardResult s scratch) := by
  simp [guardProgram, guardResult, run, execute, address, write, hn, ht, h0, h1,
    Ne.symm different]
  constructor
  · funext r
    by_cases hx : r = .x <;> by_cases hh : r = .halted <;> simp_all [write]
  · funext p
    rcases p with ⟨cell, choice⟩
    by_cases hc : cell = cursor <;> by_cases hn : cell = scratch <;>
      cases choice <;> simp_all [write]

theorem guard_traps_iff (s : State) (scratch cursor : Nat)
    (hn : s.registers .scratch = .address scratch)
    (ht : s.registers .transition = .address cursor)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true) :
    run guardProgram s = none ↔ cursor = scratch := by
  by_cases h : cursor = scratch
  · subst cursor
    simp [guard_sentinel_traps s scratch hn ht h0 h1]
  · simp [guard_candidate_correct s scratch cursor hn ht h0 h1 h, h]

/-- The guard restores every candidate-table word. Only scratch is clobbered. -/
theorem guard_memory_frame (s : State) (scratch : Nat) (p : Nat × Bool) (h : p.1 ≠ scratch) :
    (guardResult s scratch).memory p = s.memory p := by
  rcases p with ⟨cell, choice⟩
  cases choice <;> simp_all [guardResult, write]

end SmcTuring.Dolan.Mov

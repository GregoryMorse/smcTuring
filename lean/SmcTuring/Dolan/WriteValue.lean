module
public import SmcTuring.Dolan.TapeStep
public import SmcTuring.Dolan.Frames

public section

namespace SmcTuring.Dolan.Mov

/-- The new symbol is supplied by Y after the linked-table loads. Unlike the
constant-symbol variant, this is one fixed five-instruction program. -/
@[expose] def writeValueProgram : List Instruction :=
  [.load .x .current .zero] ++ selection ++ [.store .current .zero .value]

theorem write_value_equivalent (s : State) (symbol : Word) (hy : s.registers .y = symbol) :
    run (writeProgram symbol) s = run writeValueProgram s := by
  change run ([.load .x .current .zero] ++
    .immediate .y symbol :: (selection ++ [.store .current .zero .value])) s =
      run ([.load .x .current .zero] ++ (selection ++ [.store .current .zero .value])) s
  apply run_insert_noop
  intro middle completed
  have unchanged := run_register_frame [.load .x .current .zero] s middle .y completed
    (by simp [keepsRegister])
  exact immediate_noop middle .y symbol (unchanged.trans hy)

theorem write_value_correct (s : State) (scratch current : Nat) (symbol : Word) (matched : Bool)
    (hn : s.registers .scratch = .address scratch)
    (hs : s.registers .current = .address current)
    (h0 : s.registers .zero = .offset false) (h1 : s.registers .one = .offset true)
    (hm : s.registers .matched = .offset matched) (hy : s.registers .y = symbol) :
    run writeValueProgram s = some (writeResult s scratch current symbol matched) := by
  calc
    _ = run (writeProgram symbol) s := (write_value_equivalent s symbol hy).symm
    _ = _ := write_program_correct s scratch current symbol matched hn hs h0 h1 hm

theorem write_result_frame (s : State) (scratch current : Nat) (symbol : Word) (matched : Bool)
    (p : Nat × Bool) (hn : p.1 ≠ scratch) (hs : p ≠ (current, false)) :
    (writeResult s scratch current symbol matched).memory p = s.memory p := by
  rcases p with ⟨cell, choice⟩
  cases choice <;> simp_all [writeResult, write]

end SmcTuring.Dolan.Mov

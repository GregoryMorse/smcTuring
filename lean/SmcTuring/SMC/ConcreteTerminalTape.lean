module
public import SmcTuring.SMC.ConcreteFreshFields

public section

namespace SmcTuring.SMC.Concrete

open Dolan

@[expose] def sentinelPrefix : List Mov.Instruction :=
  [.load .x .transition .zero,
   .store .scratch .zero .one, .store .transition .zero .zero,
   .load .halted .scratch .zero, .store .transition .zero .x,
   .store .scratch .zero .zero, .store .scratch .one .scratch,
   .load .x .scratch .halted]

@[expose] def sentinelSourceResult (s : Mov.State) : Mov.State :=
  { registers := write (write s.registers .halted (.offset false)) .x (.offset false)
    memory := write (write s.memory (0, false) (.offset false)) (0, true) (.address 0) }

theorem sentinel_prefix_correct (s : Mov.State)
    (scratch : s.registers .scratch = .address 0) (cursor : s.registers .transition = .address 0)
    (zero : s.registers .zero = .offset false) (one : s.registers .one = .offset true) :
    Mov.run sentinelPrefix s = some (sentinelSourceResult s) := by
  simp [sentinelPrefix, sentinelSourceResult, Mov.run, Mov.execute, Mov.address, write, scratch, cursor, zero, one]
  funext r
  by_cases hx : r = .x <;> by_cases hh : r = .halted <;> simp_all [write]

theorem sentinel_prefix_tape {alphabet states : Nat} (configuration : TM.Configuration alphabet states)
    (s : Mov.State) (tape : Encoding.TapeRep (Table.tapeLayout alphabet states) configuration s) :
    Encoding.TapeRep (Table.tapeLayout alphabet states) configuration (sentinelSourceResult s) := by
  constructor
  · simpa [Encoding.RegistersRep, sentinelSourceResult, write] using tape.1
  · exact Encoding.scratch_preserves_memory (Table.tapeLayout alphabet states) configuration s.memory _ _ tape.2

theorem sentinel_prefix_supported : ∀ instruction ∈ sentinelPrefix, Supported instruction := by
  simp [sentinelPrefix, Supported]

theorem sentinel_kernel_split :
    Mov.kernelProgram = sentinelPrefix ++ (.load .x .x .zero) :: (Mov.kernelProgram.drop 9) := by rfl

theorem compile_program_append (before after : List Mov.Instruction) :
    compileProgram (before ++ after) = compileProgram before ++ compileProgram after := by
  simp [compileProgram]

theorem sentinel_sites :
    LinearAt image kernelPC (compileProgram sentinelPrefix) ∧
      LinearAt image (kernelPC + ((compileProgram sentinelPrefix).length : Int))
        (compileInstruction (.load .x .x .zero)) := by
  have placed := kernel_sites.1
  rw [sentinel_kernel_split, compile_program_append, compile_program_cons] at placed
  have parts := (linear_at_append image kernelPC _ _).mp placed
  exact ⟨parts.1, ((linear_at_append image _ _ _).mp parts.2).1⟩

/-- Recover the complete two-sided output tape and the head from code words. -/
@[expose] def TapeWords {alphabet states : Nat} (configuration : TM.Configuration alphabet states) (s : State) : Prop :=
  s.memory (Virtual.registerField dataLayout .current) =
      encodeWord dataLayout.data (.address ((Table.tapeLayout alphabet states).cell configuration.head)) ∧
    ∀ position, s.memory (heapField dataLayout.data ((Table.tapeLayout alphabet states).cell position, false)) =
      encodeWord dataLayout.data (.address ((Table.tapeLayout alphabet states).symbol (configuration.tape position)))

theorem represented_tape_words {alphabet states : Nat} (configuration : TM.Configuration alphabet states)
    (source : Mov.State) (s : State) (tape : Encoding.TapeRep (Table.tapeLayout alphabet states) configuration source)
    (represented : Virtual.Rep dataLayout source s) : TapeWords configuration s := by
  constructor
  · rw [represented.1 .current, tape.1.1]
  · intro position
    rw [represented.2 _, tape.2.1 position]

structure TerminalTapeSpec {alphabet states : Nat} (configuration : TM.Configuration alphabet states)
    (start finish : State) (count : Nat) : Prop where
  executed : Executes count start finish
  terminal : finish.pc = terminalPC
  output : TapeWords configuration finish

/-- The sentinel guard only updates scratch and two temporary source registers.
Its failing final load transfers to the intended terminal without dereferencing
the invalid pointer or disturbing any tape cell or head word. -/
theorem sentinel_terminal_tape {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (configuration : TM.Configuration alphabet states) (source : Mov.State) (s : State)
    (runtime : Mov.RuntimeRep machine configuration source) (cursor : source.registers .transition = .address 0)
    (ready : Static s) (rep : Virtual.Rep dataLayout source s) (pc : s.pc = kernelPC) :
    ∃ count finish, TerminalTapeSpec configuration s finish count := by
  have site : LinearAt image s.pc (compileProgram sentinelPrefix) := by rw [pc]; exact sentinel_sites.1
  rcases program_success sentinelPrefix source (sentinelSourceResult source) s sentinel_prefix_supported ready rep site
    (sentinel_prefix_correct source runtime.1.1 cursor runtime.1.2.1 runtime.1.2.2) with ⟨middle, before⟩
  have fault : Mov.execute (.load .x .x .zero) (sentinelSourceResult source) = none := by
    simp [Mov.execute, Mov.address, sentinelSourceResult, write, runtime.1.2.1]
  have lastSite : LinearAt image middle.pc (compileInstruction (.load .x .x .zero)) := by
    rw [before.pc, pc]
    exact sentinel_sites.2
  rcases instruction_fault (.load .x .x .zero) (sentinelSourceResult source) middle before.static
    before.represented lastSite fault with ⟨count, finish, after, _⟩
  exact ⟨programCount sentinelPrefix + count, finish, before.executed.trans after.executed, after.terminal,
    represented_tape_words configuration _ finish (sentinel_prefix_tape configuration source runtime.2.1) after.represented⟩

theorem halted_scan_sentinel {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (configuration : TM.Configuration alphabet states) (source : Mov.State)
    (scanned : Mov.ScanRep machine configuration 0 source) (halted : TM.step machine configuration = none) :
    ∃ passes finish, Mov.Passes Mov.kernelProgram source finish passes ∧
      Mov.RuntimeRep machine configuration finish ∧ finish.registers .transition = .address 0 := by
  rcases Mov.scan_resolves machine configuration 0 source scanned with ⟨passes, finish, _, history, outcome⟩
  rcases outcome with ⟨represented, _⟩ | ⟨_, next, step, _⟩
  · refine ⟨passes, finish, history, represented.1, ?_⟩
    simpa [Table.cursor] using represented.2.1
  · rw [halted] at step
    cases step

/-- A completed halting TM trace reaches the intended terminal with its entire
output tape and head intact, including cells outside the original finite input. -/
theorem tm_halt_output {alphabet states : Nat} (machine : TM.Machine alphabet states) (input : List (Fin alphabet))
    (steps : Nat) (configuration : TM.Configuration alphabet states)
    (completed : TM.run machine steps (TM.initialConfiguration machine input) = some configuration)
    (halted : TM.step machine configuration = none) :
    ∃ count finish, TerminalTapeSpec configuration (initialTMState machine input) finish count := by
  rcases tm_run_correct machine input steps configuration completed with ⟨passes, source, middle, traced⟩
  rcases halted_scan_sentinel machine configuration source traced.scanned halted with
    ⟨scanPasses, sourceFinish, history, runtime, cursor⟩
  rcases kernel_passes source sourceFinish scanPasses middle history traced.static traced.represented traced.pc with
    ⟨boundary, scanning, stable, represented, atKernel⟩
  rcases sentinel_terminal_tape machine configuration sourceFinish boundary runtime cursor stable represented atKernel with
    ⟨count, finish, terminal⟩
  exact ⟨passes * kernelCount + scanPasses * kernelCount + count, finish,
    (traced.executed.trans scanning).trans terminal.executed, terminal.terminal, terminal.output⟩

theorem terminal_runs_unique (start first second : State) (firstCount secondCount : Nat)
    (a : runImage 1 image firstCount start = some first) (b : runImage 1 image secondCount start = some second)
    (firstTerminal : first.pc = terminalPC) (secondTerminal : second.pc = terminalPC) : first = second := by
  have sameCount : firstCount = secondCount := by
    by_cases equal : firstCount = secondCount
    · exact equal
    · rcases Nat.lt_or_gt_of_ne equal with before | after
      · rw [terminal_later_none start first firstCount secondCount a firstTerminal before] at b
        cases b
      · rw [terminal_later_none start second secondCount firstCount b secondTerminal after] at a
        cases a
  subst secondCount
  exact Option.some.inj (a.symm.trans b)

/-- Every actually reached terminal has the output of the corresponding halted
TM configuration; a source failure cannot discard or invent a different output. -/
theorem terminal_output_reflects {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (input : List (Fin alphabet)) (count : Nat) (finish : State)
    (reached : runImage 1 image count (initialTMState machine input) = some finish)
    (terminal : finish.pc = terminalPC) :
    ∃ steps configuration, TM.run machine steps (TM.initialConfiguration machine input) = some configuration ∧
      TM.step machine configuration = none ∧ TapeWords configuration finish := by
  have halts := (tm_terminal_iff machine input).mp ⟨count, finish, reached, terminal⟩
  rcases halts with ⟨steps, configuration, completed, halted⟩
  rcases tm_halt_output machine input steps configuration completed halted with ⟨otherCount, other, certificate⟩
  have equal := terminal_runs_unique _ finish other count otherCount reached certificate.executed.1 terminal certificate.terminal
  exact ⟨steps, configuration, completed, halted, equal.symm ▸ certificate.output⟩

end SmcTuring.SMC.Concrete

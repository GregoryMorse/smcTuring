module
public import SmcTuring.Dolan.FourSimulation

public section
namespace SmcTuring.Dolan.Mov

/-- Eight successful MOVs precede the deliberate invalid-zero load. -/
@[expose] def guardPrefix : List Instruction := guardProgram.take 8

theorem guard_prefix_zero (s : State)
    (scratch : s.registers .scratch = .address 0)
    (sentinel : s.registers .transition = .address 0)
    (zero : s.registers .zero = .offset false)
    (one : s.registers .one = .offset true) :
    ∃ finish, run guardPrefix s = some finish ∧
      finish.registers .x = .offset false ∧ finish.registers .zero = .offset false := by
  simp [guardPrefix, guardProgram, run, execute, address, write, scratch, sentinel, zero, one]

end SmcTuring.Dolan.Mov

namespace SmcTuring.Dolan.Four

/-- A completed loop prefix reaches a literal MOV load with both address
operands zero. That instruction traps; it does not return the value zero. -/
@[expose] def ZeroTrapHalts (program : List Instruction) (start : State) : Prop :=
  ∃ passes boundary before suffix trap,
    repeatRun program passes start = some boundary ∧
    program = before ++ (.load .a .a .b :: suffix) ∧
    run before boundary = some trap ∧
    trap.registers .a = .offset false ∧ trap.registers .b = .offset false ∧
    execute (.load .a .a .b) trap = none

theorem zero_trap_halts (program : List Instruction) (start : State)
    (certified : ZeroTrapHalts program start) : LoopHalts program start := by
  rcases certified with ⟨passes, boundary, before, suffix, trap, completed,
    decomposition, reached, base, offset, stopped⟩
  refine ⟨passes, boundary, completed, ?_⟩
  rw [decomposition, run_append, reached]
  simp [run, stopped]

@[expose] def zeroTrapPrefix : List Instruction :=
  compile Mov.guardPrefix ++ (fetch .a ⟨0, by decide⟩ .x ++ fetch .b (slot .x) .zero)

theorem kernel_zero_trap_decomposition :
    ∃ suffix, kernelProgram = zeroTrapPrefix ++ (.load .a .a .b :: suffix) := by
  have guard : Mov.guardProgram = Mov.guardPrefix ++ [.load .x .x .zero] := rfl
  simp only [kernelProgram, Mov.kernelProgram, guard, compile, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, compileInstruction]
  simp only [zeroTrapPrefix, compile, List.append_assoc, List.cons_append, List.nil_append]
  exact ⟨_, rfl⟩

theorem sentinel_reaches_zero (source : Mov.State) (target : State)
    (rep : Coherent source target ⟨0, by decide⟩)
    (scratch : source.registers .scratch = .address 0)
    (sentinel : source.registers .transition = .address 0)
    (zero : source.registers .zero = .offset false)
    (one : source.registers .one = .offset true) :
    ∃ trap, run zeroTrapPrefix target = some trap ∧
      trap.registers .a = .offset false ∧ trap.registers .b = .offset false ∧
      execute (.load .a .a .b) trap = none := by
  rcases Mov.guard_prefix_zero source scratch sentinel zero one with ⟨middle, first, hx, hz⟩
  rcases compile_success Mov.guardPrefix source middle target rep first with ⟨physical, compiled, coherent⟩
  rcases fetch_base_offset middle physical .x .zero coherent with ⟨trap, operands, _, hb, ho⟩
  have base : trap.registers .a = .offset false := by simpa [hx, encode] using hb
  have offset : trap.registers .b = .offset false := by simpa [hz, encode] using ho
  exact ⟨trap, run_composition compiled operands, base, offset,
    by simp [execute, address, base, offset]⟩

theorem tm_halt_zero_trap {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) (halted : TM.Halts machine c) :
    ZeroTrapHalts kernelProgram (initialState (Mov.initialKernelState machine c)) := by
  rcases halted with ⟨n, next, history, stopped⟩
  rcases Mov.simulate_run machine n c next _ (Mov.initial_scan_correct machine c) history with
    ⟨k, middle, first, represented⟩
  rcases Mov.scan_resolves machine next 0 middle represented with ⟨l, finish, _, rest, outcome⟩
  have sentinelRep : Mov.ScanRep machine next (Table.entries machine next.state).length finish := by
    rcases outcome with ⟨sentinel, _⟩ | ⟨_, actual, actualStep, _⟩
    · exact sentinel
    · rw [stopped] at actualStep
      cases actualStep
  have sourceRun := (Mov.passes_iff_repeat Mov.kernelProgram (k + l) _ finish).1
    (Mov.passes_append Mov.kernelProgram first rest)
  have simulated := repeat_compiles Mov.kernelProgram (k + l) _ _
    (initial_coherent (Mov.initialKernelState machine c))
  rw [sourceRun] at simulated
  rcases simulated with ⟨physical, completed, coherent⟩
  have sentinel : finish.registers .transition = .address 0 := by
    simpa [Table.cursor] using sentinelRep.2.1
  rcases sentinel_reaches_zero finish physical coherent sentinelRep.1.1.1 sentinel
    sentinelRep.1.1.2.1 sentinelRep.1.1.2.2 with ⟨trap, reached, base, offset, fault⟩
  rcases kernel_zero_trap_decomposition with ⟨suffix, decomposition⟩
  exact ⟨k + l, physical, zeroTrapPrefix, suffix, trap, completed, decomposition,
    reached, base, offset, fault⟩

theorem zero_trap_halting_iff {alphabet states : Nat} (machine : TM.Machine alphabet states)
    (c : TM.Configuration alphabet states) :
    ZeroTrapHalts kernelProgram (initialState (Mov.initialKernelState machine c)) ↔ TM.Halts machine c := by
  constructor
  · intro certified
    exact (Mov.kernel_halting_iff machine c).1
      ((compiled_halting_iff Mov.kernelProgram _ _ (initial_coherent _)).1
        (zero_trap_halts kernelProgram _ certified))
  · exact tm_halt_zero_trap machine c

/-- Four literal MOV registers, a fixed 2,252-instruction body, one backedge,
and a certified zero-address fault exactly when the represented TM halts. -/
theorem four_register_mov_certified_simulation : ∃ program : List Instruction,
    program.length = 2252 ∧
    ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet)),
      let c := TM.initialConfiguration machine input
      let s := initialState (Mov.initialKernelState machine c)
      (LoopHalts program s ↔ TM.Halts machine c) ∧
      (ZeroTrapHalts program s ↔ TM.Halts machine c) ∧
      (LoopDiverges program s ↔ TM.Diverges machine c) := by
  refine ⟨kernelProgram, kernel_length, ?_⟩
  intro alphabet states machine input
  exact ⟨(compiled_halting_iff Mov.kernelProgram _ _ (initial_coherent _)).trans
      (Mov.kernel_halting_iff machine _), zero_trap_halting_iff machine _,
    (compiled_divergence_iff Mov.kernelProgram _ _ (initial_coherent _)).trans
      (Mov.kernel_divergence_iff machine _)⟩

end SmcTuring.Dolan.Four

module
public import SmcTuring.SMC.ConcretePrograms
public import SmcTuring.Dolan.Simulation

public section

namespace SmcTuring.SMC.Concrete

open Dolan

@[expose] def kernelCount : Nat := programCount Mov.kernelProgram + 3

theorem kernel_count_positive : 0 < kernelCount := by unfold kernelCount; omega

theorem kernel_sites :
    LinearAt image kernelPC (compileProgram Mov.kernelProgram) ∧
    LinearAt image (kernelPC + ((compileProgram Mov.kernelProgram).length : Int)) (callProgram (.operand loopField)) :=
  (linear_at_append image kernelPC _ _).mp kernel_placement

theorem static_loop_target (s : State) (ready : Static s) : s.memory loopField = kernelPC := by
  simpa [loopField, metadataValue] using ready 35 (by decide)

@[expose] def loopCallResult (s : State) : State := run 1 (callProgram (.operand loopField)) s

theorem loop_call_effect (s : State) (ready : Static s) : loopCallResult s =
    { s with stack := returnField, pc := kernelPC, memory := write s.memory returnField (s.pc + 3) } := by
  rw [loopCallResult, callProgram, reset_call_operand_correct 1 topField returnField loopField s (static_top s ready),
    static_loop_target s ready]

theorem loop_call_static (s : State) (ready : Static s) : Static (loopCallResult s) := by
  simpa only [Static, loop_call_effect s ready, returnField] using static_dynamic_write s 26 (s.pc + 3) ready (by decide)

theorem loop_call_source (source : Mov.State) (s : State) (ready : Static s) (rep : Virtual.Rep dataLayout source s) :
    Virtual.Rep dataLayout source (loopCallResult s) := by
  simpa only [Virtual.Rep, loop_call_effect s ready, returnField] using metadata_source_frame source s 26 (s.pc + 3) rep

theorem loop_call_execute (s : State) (ready : Static s)
    (site : LinearAt image s.pc (callProgram (.operand loopField))) : Executes 3 s (loopCallResult s) := by
  apply reset_call_image 1 image topField returnField (.operand loopField) s
  · exact ⟨site.1, site.2.1, trivial⟩
  · simpa [Int.add_assoc] using site.2.2.1
  · exact static_top s ready
  · exact meta_is_code 25 (by decide)
  · exact meta_is_code 26 (by decide)

structure KernelSpec (next : Mov.State) (start finish : State) : Prop where
  executed : Executes kernelCount start finish
  static : Static finish
  represented : Virtual.Rep dataLayout next finish
  pc : finish.pc = kernelPC

/-- One complete source kernel pass includes the actual code-backed backedge.
All instruction/owner/callee placement comes from the fixed constructed image. -/
theorem kernel_success (source next : Mov.State) (s : State) (ready : Static s)
    (rep : Virtual.Rep dataLayout source s) (pc : s.pc = kernelPC) (success : Mov.run Mov.kernelProgram source = some next) :
    ∃ finish, KernelSpec next s finish := by
  have bodySite : LinearAt image s.pc (compileProgram Mov.kernelProgram) := by rw [pc]; exact kernel_sites.1
  rcases program_success Mov.kernelProgram source next s kernel_supported ready rep bodySite success with ⟨middle, body⟩
  have tailSite : LinearAt image middle.pc (callProgram (.operand loopField)) := by
    rw [body.pc, pc]
    exact kernel_sites.2
  refine ⟨loopCallResult middle, body.executed.trans (loop_call_execute middle body.static tailSite),
    loop_call_static middle body.static, loop_call_source next middle body.static body.represented, ?_⟩
  rw [loop_call_effect middle body.static]

theorem kernel_fault (source : Mov.State) (s : State) (ready : Static s) (rep : Virtual.Rep dataLayout source s)
    (pc : s.pc = kernelPC) (fault : Mov.run Mov.kernelProgram source = none) :
    ∃ count finish, ProgramFaultSpec s finish count (programCount Mov.kernelProgram) := by
  apply program_fault Mov.kernelProgram source s kernel_supported ready rep
  · rw [pc]
    exact kernel_sites.1
  · exact fault

end SmcTuring.SMC.Concrete

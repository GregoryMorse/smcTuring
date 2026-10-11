module
public import SmcTuring.SMC.ReadRoutines

public section

namespace SmcTuring.SMC

theorem read_routine_store_tail (wordImage : Image) (label routine constant returnField : Int)
    (placed : ReadRoutinePlacement wordImage label routine constant returnField) :
    LinearAt wordImage (routine + 3) ([.store (.operand label)] ++ stackResetProgram constant) := by
  have tail : LinearAt wordImage (routine + 1 + 1 + 1)
      ([.store (.operand label)] ++ stackResetProgram constant) := placed.body.2.2.2
  simpa [Int.add_assoc] using tail

@[expose] def storeInvocationResult (label routine returnField : Int) (s : State) : State :=
  { s with
    stack := returnField
    pc := s.pc + 3
    memory := write (write s.memory (s.memory label) s.acc) returnField (routine + 7) }

/-- The store entry is the last instruction of the shared read body. Both
operations therefore use one mutable MOFFS operand, with real code-writing
CALL/return paths. Writes to return and stack-top fields are excluded here. -/
theorem store_routine_correct (wordBytes : Int) (image : Image)
    (label routine constant returnField : Int) (s : State)
    (placed : ReadRoutinePlacement image label routine constant returnField)
    (entryReset : LinearAt image s.pc (stackResetProgram constant))
    (entryCall : image.headers (s.pc + 2) = some (.call (.fixed (routine + 3)), s.pc + 3))
    (top : s.memory constant = returnField + wordBytes)
    (constantSeparate : constant ≠ returnField) (labelSeparate : label ≠ returnField)
    (targetSeparate : s.memory label ≠ returnField) (targetConstant : s.memory label ≠ constant)
    (constantCode : image.codeField constant) (returnCode : image.codeField returnField)
    (targetCode : image.codeField (s.memory label)) :
    runImage wordBytes image 7 s = some (storeInvocationResult label routine returnField s) ∧
      PureSteps wordBytes image 7 s := by
  let invoked : State :=
    { s with stack := returnField, pc := routine + 3, memory := write s.memory returnField (s.pc + 3) }
  have entry := reset_call_image wordBytes image constant returnField (.fixed (routine + 3)) s
    entryReset entryCall top constantCode returnCode
  have entryRun : runImage wordBytes image 3 s = some invoked := by
    simpa only [reset_call_correct wordBytes constant returnField (routine + 3) s top] using entry.1
  have sequential : NonBranching ([.store (.operand label)] ++ stackResetProgram constant) := by
    simp [NonBranching, stackResetProgram, Header.Sequential]
  have body := linear_image_execution wordBytes image ([.store (.operand label)] ++ stackResetProgram constant)
    invoked (read_routine_store_tail image label routine constant returnField placed) sequential
  let ready : State :=
    { invoked with
      stack := returnField + wordBytes
      pc := routine + 6
      memory := write invoked.memory (s.memory label) s.acc }
  have bodyEffect : run wordBytes ([.store (.operand label)] ++ stackResetProgram constant) invoked = ready := by
    rw [run_append, stack_reset_correct]
    simp [run, decode, Address.eval, execute, ready, invoked, write,
      constantSeparate, labelSeparate, Ne.symm targetConstant, top, Int.add_assoc]
  have bodyRun : runImage wordBytes image 3 invoked = some ready := by
    simpa only [show ([Header.store (.operand label)] ++ stackResetProgram constant).length = 3 by rfl, bodyEffect] using body.1
  have bodyPure : PureSteps wordBytes image 3 invoked := by
    apply body.2.mpr
    rw [pure_append]
    constructor
    · simpa [PureRun, WritesCode, footprint, decode, Address.eval, invoked, write, labelSeparate] using targetCode
    · exact stack_reset_pure _ _ _ _ constantCode
  have last := image_single wordBytes image (.call (.operand returnField)) (routine + 7) ready placed.returnCall
  have lastEffect : execute wordBytes (decode (.call (.operand returnField)) ready) (routine + 7) ready =
      storeInvocationResult label routine returnField s := by
    simp [storeInvocationResult, ready, invoked, decode, Address.eval, execute, write, Ne.symm targetSeparate]
    rw [writes_commute s.memory returnField (s.memory label) (s.pc + 3) s.acc (Ne.symm targetSeparate), write_overwrite]
  have lastRun : runImage wordBytes image 1 ready = some (storeInvocationResult label routine returnField s) := by
    simpa only [lastEffect] using last.1
  have lastPure : PureSteps wordBytes image 1 ready := by
    apply last.2.mpr
    simp [WritesCode, footprint, decode, ready, returnCode]
  have tailRun : runImage wordBytes image 4 invoked = some (storeInvocationResult label routine returnField s) := by
    rw [show (4 : Nat) = 3 + 1 by rfl, run_image_add, bodyRun, Option.bind_some]
    exact lastRun
  constructor
  · rw [show (7 : Nat) = 3 + 4 by rfl, run_image_add, entryRun, Option.bind_some]
    exact tailRun
  · rw [show (7 : Nat) = 3 + 4 by rfl, pure_steps_composition wordBytes image 3 4 s invoked entryRun]
    refine ⟨entry.2, ?_⟩
    rw [show (4 : Nat) = 3 + 1 by rfl, pure_steps_composition wordBytes image 3 1 invoked ready bodyRun]
    exact ⟨bodyPure, lastPure⟩

end SmcTuring.SMC

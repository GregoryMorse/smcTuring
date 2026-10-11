module
public import SmcTuring.SMC.ExecutionComposition

public section

namespace SmcTuring.SMC

/-- A shared DEFADDR body, followed by a code-backed return CALL. Each label
has one body containing its final mutable MOFFS instruction. Call sites contain
only stack reset and direct CALL; they do not duplicate that operand. -/
structure ReadRoutinePlacement (image : Image) (label routine constant returnField : Int) : Prop where
  body : LinearAt image routine (readProgram label ++ stackResetProgram constant)
  returnCall : image.headers (routine + 6) = some (.call (.operand returnField), routine + 7)
  owner : image.templatePC label = routine + 3

@[expose] def readInvocationResult (label routine returnField : Int) (s : State) : State :=
  { s with
    acc := s.memory (s.memory label)
    stack := returnField
    pc := s.pc + 3
    memory := write s.memory returnField (routine + 7) }

theorem read_routine_correct (wordBytes : Int) (image : Image)
    (label routine constant returnField : Int) (s : State)
    (placed : ReadRoutinePlacement image label routine constant returnField)
    (entryReset : LinearAt image s.pc (stackResetProgram constant))
    (entryCall : image.headers (s.pc + 2) = some (.call (.fixed routine), s.pc + 3))
    (top : s.memory constant = returnField + wordBytes)
    (constantSeparate : constant ≠ returnField) (labelSeparate : label ≠ returnField)
    (targetSeparate : s.memory label ≠ returnField)
    (constantCode : image.codeField constant) (returnCode : image.codeField returnField)
    (labelCode : image.codeField label) (targetCode : image.codeField (s.memory label)) :
    runImage wordBytes image 10 s = some (readInvocationResult label routine returnField s) ∧
      PureSteps wordBytes image 10 s := by
  let invoked : State :=
    { s with stack := returnField, pc := routine, memory := write s.memory returnField (s.pc + 3) }
  have entry := reset_call_image wordBytes image constant returnField (.fixed routine) s
    entryReset entryCall top constantCode returnCode
  have entryRun : runImage wordBytes image 3 s = some invoked := by
    simpa only [reset_call_correct wordBytes constant returnField routine s top] using entry.1
  have sequential : NonBranching (readProgram label ++ stackResetProgram constant) := by
    simp [NonBranching, readProgram, stackResetProgram, Header.Sequential]
  have body := linear_image_execution wordBytes image (readProgram label ++ stackResetProgram constant)
    invoked placed.body sequential
  let ready : State :=
    { invoked with
      acc := s.memory (s.memory label)
      stack := returnField + wordBytes
      pc := routine + 6 }
  have bodyEffect : run wordBytes (readProgram label ++ stackResetProgram constant) invoked = ready := by
    rw [run_append, read_correct, stack_reset_correct]
    simp [ready, invoked, write, constantSeparate, labelSeparate, targetSeparate, top, Int.add_assoc]
  have bodyRun : runImage wordBytes image 6 invoked = some ready := by
    simpa only [show (readProgram label ++ stackResetProgram constant).length = 6 by rfl, bodyEffect] using body.1
  have bodyPure : PureSteps wordBytes image 6 invoked := by
    apply body.2.mpr
    rw [pure_append]
    constructor
    · apply read_pure
      · exact labelCode
      · simpa [invoked, write, labelSeparate] using targetCode
    · exact stack_reset_pure _ _ _ _ constantCode
  have last := image_single wordBytes image (.call (.operand returnField)) (routine + 7) ready placed.returnCall
  have lastEffect : execute wordBytes (decode (.call (.operand returnField)) ready) (routine + 7) ready =
      readInvocationResult label routine returnField s := by
    simp [readInvocationResult, ready, invoked, decode, Address.eval, execute]
  have lastRun : runImage wordBytes image 1 ready = some (readInvocationResult label routine returnField s) := by
    simpa only [lastEffect] using last.1
  have lastPure : PureSteps wordBytes image 1 ready := by
    apply last.2.mpr
    simp [WritesCode, footprint, decode, ready, returnCode]
  have tailRun : runImage wordBytes image 7 invoked = some (readInvocationResult label routine returnField s) := by
    rw [show (7 : Nat) = 6 + 1 by rfl, run_image_add, bodyRun, Option.bind_some]
    exact lastRun
  constructor
  · rw [show (10 : Nat) = 3 + 7 by rfl, run_image_add, entryRun, Option.bind_some]
    exact tailRun
  · rw [show (10 : Nat) = 3 + 7 by rfl, pure_steps_composition wordBytes image 3 7 s invoked entryRun]
    refine ⟨entry.2, ?_⟩
    rw [show (7 : Nat) = 6 + 1 by rfl, pure_steps_composition wordBytes image 6 1 invoked ready bodyRun]
    exact ⟨bodyPure, lastPure⟩

end SmcTuring.SMC

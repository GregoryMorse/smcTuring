module
public import SmcTuring.SMC.Execution

public section

namespace SmcTuring.SMC

theorem run_image_add (wordBytes : Int) (image : Image) (first second : Nat) (s : State) :
    runImage wordBytes image (first + second) s =
      (runImage wordBytes image first s).bind (runImage wordBytes image second) := by
  induction first generalizing s with
  | zero => simp [runImage]
  | succ first ih =>
    cases firstStep : step wordBytes image s with
    | none => simp [runImage, Nat.succ_add, firstStep]
    | some next => simpa [runImage, Nat.succ_add, firstStep] using ih next

theorem pure_steps_composition (wordBytes : Int) (image : Image) (first second : Nat)
    (s middle : State) (completed : runImage wordBytes image first s = some middle) :
    PureSteps wordBytes image (first + second) s ↔
      PureSteps wordBytes image first s ∧ PureSteps wordBytes image second middle := by
  induction first generalizing s with
  | zero =>
    simp only [runImage, Option.some.injEq] at completed
    subst middle
    simp [PureSteps]
  | succ first ih =>
    cases fetched : fetch image s with
    | none => simp [runImage, step, fetched] at completed
    | some entry =>
      rcases entry with ⟨instruction, next⟩
      have tail : runImage wordBytes image first (execute wordBytes instruction next s) = some middle := by
        simpa [runImage, step, fetched] using completed
      have correct := ih (execute wordBytes instruction next s) tail
      simpa [PureSteps, fetched, Nat.succ_add, and_assoc] using
        and_congr_right (fun (_ : WritesCode image.codeField wordBytes instruction s) => correct)

theorem image_single (wordBytes : Int) (image : Image) (header : Header) (next : Int) (s : State)
    (placed : image.headers s.pc = some (header, next)) :
    runImage wordBytes image 1 s = some (execute wordBytes (decode header s) next s) ∧
      (PureSteps wordBytes image 1 s ↔ WritesCode image.codeField wordBytes (decode header s) s) := by
  simp [runImage, PureSteps, step, fetch, placed]

/-- A stack reset and CALL are fetched from the image and actually follow
the selected target. The return-address write lands in the code field. -/
theorem reset_call_image (wordBytes : Int) (image : Image) (constant returnField : Int)
    (destination : Address) (s : State)
    (reset : LinearAt image s.pc (stackResetProgram constant))
    (call : image.headers (s.pc + 2) = some (.call destination, s.pc + 3))
    (top : s.memory constant = returnField + wordBytes)
    (constantCode : image.codeField constant) (returnCode : image.codeField returnField) :
    runImage wordBytes image 3 s =
      some (run wordBytes (stackResetProgram constant ++ [.call destination]) s) ∧
      PureSteps wordBytes image 3 s := by
  have sequential : NonBranching (stackResetProgram constant) := by
    simp [NonBranching, stackResetProgram, Header.Sequential]
  have first := linear_image_execution wordBytes image (stackResetProgram constant) s reset sequential
  have firstRun : runImage wordBytes image 2 s = some (run wordBytes (stackResetProgram constant) s) := first.1
  let middle := run wordBytes (stackResetProgram constant) s
  have middlePC : middle.pc = s.pc + 2 := by simp [middle, stack_reset_correct]
  have last := image_single wordBytes image (.call destination) (s.pc + 3) middle (by simpa only [middlePC] using call)
  constructor
  · rw [show (3 : Nat) = 2 + 1 by rfl, run_image_add, firstRun, Option.bind_some, last.1, run_append]
    simp [middle, run, middlePC, Int.add_assoc]
  · rw [show (3 : Nat) = 2 + 1 by rfl, pure_steps_composition wordBytes image 2 1 s middle firstRun]
    constructor
    · exact first.2.mpr (stack_reset_pure _ _ _ _ constantCode)
    · apply last.2.mpr
      simp [WritesCode, footprint, decode, middle, stack_reset_correct, top, returnCode]

end SmcTuring.SMC

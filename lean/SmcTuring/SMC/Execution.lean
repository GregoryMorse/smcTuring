module
public import SmcTuring.SMC.LoweringCorrect

public section

namespace SmcTuring.SMC

/-- Execution fetches each header from the image and resolves its operands
from the current memory. It follows the executed instruction's actual PC. -/
@[expose] def runImage (wordBytes : Int) (image : Image) : Nat → State → Option State
  | 0, s => some s
  | count + 1, s => (step wordBytes image s).bind (runImage wordBytes image count)

@[expose] def PureSteps (wordBytes : Int) (image : Image) : Nat → State → Prop
  | 0, _ => True
  | count + 1, s =>
    match fetch image s with
    | none => False
    | some (instruction, next) => WritesCode image.codeField wordBytes instruction s ∧
        PureSteps wordBytes image count (execute wordBytes instruction next s)

@[expose] def Header.Sequential : Header → Prop
  | .call _ => False
  | _ => True

@[expose] def NonBranching (program : List Header) : Prop :=
  ∀ header ∈ program, header.Sequential

theorem sequential_pc (wordBytes : Int) (header : Header) (next : Int) (s : State)
    (sequential : header.Sequential) : (execute wordBytes (decode header s) next s).pc = next := by
  cases header <;> simp_all [Header.Sequential, execute, decode]

/-- Placement evidence for a linear effect block in a word-level image.
This does not discharge physical byte ownership or native decoder obligations. -/
@[expose] def LinearAt (image : Image) : Int → List Header → Prop
  | _, [] => True
  | pc, header :: rest => image.headers pc = some (header, pc + 1) ∧ LinearAt image (pc + 1) rest

theorem linear_image_execution (wordBytes : Int) (image : Image) (program : List Header) (s : State)
    (placement : LinearAt image s.pc program) (sequential : NonBranching program) :
    runImage wordBytes image program.length s = some (run wordBytes program s) ∧
      (PureSteps wordBytes image program.length s ↔ PureRun image.codeField wordBytes program s) := by
  induction program generalizing s with
  | nil => exact ⟨rfl, Iff.rfl⟩
  | cons header rest ih =>
    have headSequential := sequential header (by simp)
    have tailSequential : NonBranching rest := fun instruction member => sequential instruction (by simp [member])
    have pc := sequential_pc wordBytes header (s.pc + 1) s headSequential
    have tailPlacement : LinearAt image (execute wordBytes (decode header s) (s.pc + 1) s).pc rest := by
      rw [pc]
      exact placement.2
    have fetched : fetch image s = some (decode header s, s.pc + 1) := by
      simp [fetch, placement.1]
    have tail := ih (execute wordBytes (decode header s) (s.pc + 1) s) tailPlacement tailSequential
    simp only [List.length_cons, runImage, step, fetched, Option.map_some, Option.bind_some, run,
      PureSteps, PureRun]
    exact ⟨tail.1, and_congr_right (fun _ => tail.2)⟩

theorem pure_run_mono (first second : Int → Prop) (wordBytes : Int) (program : List Header) (s : State)
    (included : ∀ field, first field → second field) (pure : PureRun first wordBytes program s) :
    PureRun second wordBytes program s := by
  induction program generalizing s with
  | nil => trivial
  | cons header rest ih =>
    exact ⟨⟨pure.1.1, fun field member => included field (pure.1.2 field member)⟩, ih _ pure.2⟩

namespace Lowering

open Dolan

theorem instruction_non_branching (layout : OperandLayout) (instruction : Four.Instruction) :
    NonBranching (compileInstruction layout instruction) := by
  cases instruction <;>
    simp [NonBranching, compileInstruction, addressProgram, copyProgram, readProgram, Header.Sequential]

theorem compile_non_branching (layout : OperandLayout) (program : List Four.Instruction) :
    NonBranching (compile layout program) := by
  intro header member
  rcases List.mem_flatMap.mp member with ⟨instruction, _, instructionMember⟩
  exact instruction_non_branching layout instruction header instructionMember

/-- A conditional embedding of a successful lowered block into an actual
word-image execution. Placement and storage-template coverage are independent
layout obligations; neither is inferred from an executable-page permission. -/
theorem compile_image_run (layout : OperandLayout) (wordBytes : Int) (image : Image)
    (program : List Four.Instruction) (source next : Four.State) (target : State)
    (rep : Rep layout source target) (success : Four.run program source = some next)
    (placement : LinearAt image target.pc (compile layout program))
    (storage : ∀ field, Code layout field → image.codeField field) :
    ∃ result, runImage wordBytes image (compile layout program).length target = some result ∧
      Rep layout next result ∧ PureSteps wordBytes image (compile layout program).length target := by
  have effect := compile_run layout wordBytes program source next target rep success
  have execution := linear_image_execution wordBytes image (compile layout program) target placement
    (compile_non_branching layout program)
  exact ⟨_, execution.1, effect.1,
    execution.2.mpr (pure_run_mono _ _ _ _ _ storage effect.2)⟩

end Lowering

@[expose] def ChangesCode (codeField : Int → Prop) (wordBytes : Int)
    (instruction : Instruction) (next : Int) (s : State) : Prop :=
  ∃ field, codeField field ∧ (execute wordBytes instruction next s).memory field ≠ s.memory field

@[expose] def ChangesInRun (codeField : Int → Prop) (wordBytes : Int) : List Header → State → Prop
  | [], _ => False
  | header :: rest, s => ChangesCode codeField wordBytes (decode header s) (s.pc + 1) s ∨
      ChangesInRun codeField wordBytes rest (execute wordBytes (decode header s) (s.pc + 1) s)

theorem boundary_change_has_instruction_change (codeField : Int → Prop) (wordBytes : Int)
    (program : List Header) (s : State) (field : Int) (code : codeField field)
    (different : (run wordBytes program s).memory field ≠ s.memory field) :
    ChangesInRun codeField wordBytes program s := by
  induction program generalizing s with
  | nil => exact False.elim (different rfl)
  | cons header rest ih =>
    by_cases unchanged : (execute wordBytes (decode header s) (s.pc + 1) s).memory field = s.memory field
    · apply Or.inr
      apply ih
      simpa only [run, unchanged] using different
    · exact Or.inl ⟨field, code, unchanged⟩

end SmcTuring.SMC

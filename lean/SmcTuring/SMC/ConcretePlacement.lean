module
public import SmcTuring.SMC.ConcreteReadOps

public section

namespace SmcTuring.SMC

theorem linear_at_indexed (image : Image) (pc : Int) (program : List Header)
    (placed : ∀ index, index < program.length → image.headers (pc + (index : Int)) =
      (program[index]?).map (fun header => (header, pc + (index : Int) + 1))) :
    LinearAt image pc program := by
  induction program generalizing pc with
  | nil => trivial
  | cons header rest ih =>
    have first := placed 0 (by simp)
    simp only [List.getElem?_cons_zero, Int.natCast_zero, Int.add_zero, Option.map_some] at first
    refine ⟨first, ih (pc + 1) ?_⟩
    intro index small
    have later := placed (index + 1) (by simpa using Nat.succ_lt_succ small)
    simpa [List.getElem?_cons_succ, Int.add_assoc, Int.add_left_comm, Int.add_comm] using later

theorem linear_at_append (image : Image) (pc : Int) (first second : List Header) :
    LinearAt image pc (first ++ second) ↔
      LinearAt image pc first ∧ LinearAt image (pc + (first.length : Int)) second := by
  induction first generalizing pc with
  | nil => simp [LinearAt]
  | cons header rest ih =>
    simpa [LinearAt, Int.add_assoc, Int.add_left_comm, Int.add_comm, and_assoc] using
      and_congr_right (fun (_ : image.headers pc = some (header, pc + 1)) => ih (pc + 1))

namespace Concrete

theorem kernel_header (index : Nat) :
    headers (kernelPC + (index : Int)) =
      (kernelProgram[index]?).map (fun header => (header, kernelPC + (index : Int) + 1)) := by
  have nonnegative : 0 ≤ kernelPC + (index : Int) := by simp [kernelPC]; omega
  have natural : (kernelPC + (index : Int)).toNat = 264 + index := by simp only [kernelPC]; omega
  have first : ¬ 264 + index < 184 := by omega
  have second : ¬ 264 + index < 224 := by omega
  have third : ¬ 264 + index < 264 := by omega
  have relative : 264 + index - 264 = index := by omega
  simp only [headers, nonnegative, ite_true, natural, controlHeader, first, second, third, ite_false, relative]

theorem kernel_subblock (start : Nat) (block : List Header)
    (lookup : ∀ index, index < block.length → kernelProgram[start + index]? = block[index]?) :
    LinearAt image (kernelPC + (start : Int)) block := by
  apply linear_at_indexed
  intro index small
  have actual := kernel_header (start + index)
  rw [lookup index small] at actual
  simpa [image, Int.add_assoc] using actual

theorem kernel_placement : LinearAt image kernelPC kernelProgram := by
  apply linear_at_indexed
  intro index _
  exact kernel_header index

theorem guard_subblock (sense : Bool) (start : Nat) (block : List Header)
    (bounded : start + block.length ≤ 37)
    (lookup : ∀ index, index < block.length → (guardProgram sense)[start + index]? = block[index]?) :
    LinearAt image (guardPC sense + (start : Int)) block := by
  apply linear_at_indexed
  intro index small
  have actual := guard_header sense (start + index) (by omega)
  rw [lookup index small] at actual
  simpa [image, Int.add_assoc] using actual

structure GuardRead where
  start : Nat
  reader : Nat
  operation : Operation

@[expose] def guardRead (sense : Bool) (index : Fin 7) : GuardRead :=
  let cont := if sense then 17 else 16
  let stop := if sense then 16 else 17
  match index.val with
  | 0 => ⟨5, 13, .assign scratchField⟩
  | 1 => ⟨9, 14, .subtract scratchField⟩
  | 2 => ⟨13, 15, .assign maskField⟩
  | 3 => ⟨18, cont, .assign selectedField⟩
  | 4 => ⟨22, stop, .bitXor selectedField⟩
  | 5 => ⟨26, 18, .bitAnd selectedField⟩
  | _ => ⟨30, cont, .bitXor selectedField⟩

theorem guard_read_site (sense : Bool) (index : Fin 7) :
    let block := guardRead sense index
    LinearAt image (guardPC sense + (block.start : Int)) (readOp block.reader block.operation.header) := by
  apply guard_subblock
  · rcases index with ⟨index, small⟩
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 := by omega
    rcases choices with h | h | h | h | h | h | h <;> subst index <;> cases sense <;>
      simp only [guardRead] <;> decide
  · intro i small
    have length : (readOp (guardRead sense index).reader (guardRead sense index).operation.header).length = 4 := rfl
    rw [length] at small
    have choicesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases index with ⟨index, bounded⟩
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 := by omega
    rcases choices with h | h | h | h | h | h | h <;> subst index <;>
      rcases choicesI with hi | hi | hi | hi <;> subst i <;> cases sense <;> rfl

theorem guard_read_bounded (sense : Bool) (index : Fin 7) : (guardRead sense index).reader < 22 := by
  rcases index with ⟨index, small⟩
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 := by omega
  rcases choices with h | h | h | h | h | h | h <;> subst index <;> cases sense <;>
    simp only [guardRead] <;> decide

theorem guard_read_code (sense : Bool) (index : Fin 7) : image.codeField (guardRead sense index).operation.field := by
  rcases index with ⟨index, small⟩
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 := by omega
  rcases choices with h | h | h | h | h | h | h <;> subst index <;> cases sense <;>
    simp only [guardRead, Operation.field, image, Code] <;> decide

theorem guard_read_dynamic (sense : Bool) (index : Fin 7) (slot : Nat) (stable : StaticSlot slot) :
    metaField slot ≠ (guardRead sense index).operation.field := by
  rcases index with ⟨index, small⟩
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 := by omega
  rcases choices with h | h | h | h | h | h | h <;> subst index <;> cases sense <;>
    simp only [guardRead, Operation.field, scratchField, maskField, selectedField, metaField, StaticSlot] at * <;> omega

theorem guard_read_outside (sense : Bool) (index : Fin 7) :
    ¬ codeField dataLayout.data (guardRead sense index).operation.field := by
  rcases index with ⟨index, small⟩
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 := by omega
  rcases choices with h | h | h | h | h | h | h <;> subst index <;> cases sense <;>
    first | exact metadata_outside_data 33 | exact metadata_outside_data 32 | exact metadata_outside_data 34

@[expose] def guardCaptureProgram (sense : Bool) : List Header :=
  readProgram (captureLabel sense) ++ [.store (.fixed resumeField)]

theorem guard_capture_site (sense : Bool) : LinearAt image (guardPC sense) (guardCaptureProgram sense) := by
  have placed := guard_subblock sense 0 (guardCaptureProgram sense) (by cases sense <;> decide) (by
    intro index small
    have bound : index < 5 := small
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases choices with h | h | h | h | h <;> subst index <;> cases sense <;> rfl)
  simpa using placed

theorem guard_sbb_site (sense : Bool) :
    image.headers (guardPC sense + 17) = some (.subtractBorrowZero maskField, guardPC sense + 18) := by
  have actual := guard_header sense 17 (by decide)
  cases sense <;> simpa [image, guardProgram, readProgram, readOp, callProgram, stackResetProgram, guardPC] using actual

theorem guard_final_call_site (sense : Bool) :
    LinearAt image (guardPC sense + 34) (callProgram (.operand selectedField)) := by
  apply guard_subblock sense 34
  · decide
  · intro index small
    have bound : index < 3 := small
    have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases choices with h | h | h <;> subst index <;> cases sense <;> rfl

end Concrete
end SmcTuring.SMC

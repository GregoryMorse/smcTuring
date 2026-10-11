module
public import SmcTuring.SMC.VirtualInstructions
public import SmcTuring.Dolan.Kernel

public section

namespace SmcTuring.SMC.Concrete

open Dolan

/-- Word addresses for the unbounded witness. Thirteen nonnegative fields are
logical registers; subsequent fields are the two-word source heap. Metadata
occupies exactly -1 through -38, separate from that data grid. -/
@[expose] def dataLayout : Virtual.Layout :=
  { data := { base := 0, stride := 1, reserved := 13,
              base_nonnegative := by decide, stride_positive := by decide, enough_reserved := by decide }
    enoughRegisters := by decide }

@[expose] def metaField (index : Nat) : Int := -((index : Int) + 1)
@[expose] def readerLabel (index : Nat) : Int := metaField index
@[expose] def readerPC (index : Nat) : Int := 8 * (index : Int)
@[expose] def captureLabel (sense : Bool) : Int := metaField (if sense then 24 else 23)
@[expose] def guardPC (sense : Bool) : Int := if sense then 224 else 184
@[expose] def kernelPC : Int := 264
@[expose] def terminalPC : Int := 1000000

@[expose] def topField : Int := metaField 25
@[expose] def returnField : Int := metaField 26
@[expose] def candidateField : Int := metaField 27
@[expose] def boundaryField : Int := metaField 28
@[expose] def zeroField : Int := metaField 29
@[expose] def resumeField : Int := metaField 30
@[expose] def terminalField : Int := metaField 31
@[expose] def maskField : Int := metaField 32
@[expose] def scratchField : Int := metaField 33
@[expose] def selectedField : Int := metaField 34
@[expose] def loopField : Int := metaField 35
@[expose] def offsetZeroField : Int := metaField 36
@[expose] def offsetOneField : Int := metaField 37
@[expose] def pointerLabel : Int := readerLabel 22

@[expose] def callProgram (target : Address) : List Header :=
  stackResetProgram topField ++ [.call target]

@[expose] def readOp (reader : Nat) (operation : Header) : List Header :=
  callProgram (.fixed (readerPC reader)) ++ [operation]

@[expose] def readerProgram (reader : Nat) : List Header :=
  readProgram (readerLabel reader) ++ stackResetProgram topField ++ [.call (.operand returnField)]

/-- Two shared guards. `true` checks the offset tag (targets swapped), and
`false` checks the calculated base. Each saves the caller's return PC first. -/
@[expose] def guardProgram (sense : Bool) : List Header :=
  let cont := if sense then 17 else 16
  let stop := if sense then 16 else 17
  readProgram (captureLabel sense) ++ [.store (.fixed resumeField)] ++
    readOp 13 (.store (.fixed scratchField)) ++ readOp 14 (.subtract scratchField) ++
    readOp 15 (.store (.fixed maskField)) ++ [.subtractBorrowZero maskField] ++
    readOp cont (.store (.fixed selectedField)) ++ readOp stop (.bitXor selectedField) ++
    readOp 18 (.bitAnd selectedField) ++ readOp cont (.bitXor selectedField) ++
    callProgram (.operand selectedField)

@[expose] def sourceRegister (r : Mov.Register) : Int := ((Four.slot r).val : Int)

@[expose] def addressProgram (base offset : Mov.Register) : List Header :=
  readOp (Four.slot offset).val (.store (.fixed candidateField)) ++ callProgram (.fixed (guardPC true)) ++
    readOp (Four.slot base).val (.store (.fixed pointerLabel)) ++
    readOp (Four.slot offset).val (.add pointerLabel) ++
    readOp 21 (.store (.fixed candidateField)) ++ callProgram (.fixed (guardPC false))

/-- Address immediates are outside this fixed kernel's grammar. Their explicit
terminal block is never used by the proved supported-kernel check. -/
@[expose] def compileInstruction : Mov.Instruction → List Header
  | .immediate dest (.offset value) =>
      readOp (if value then 20 else 19) (.store (.fixed (sourceRegister dest)))
  | .immediate _ (.address _) => callProgram (.fixed terminalPC)
  | .load dest base offset =>
      addressProgram base offset ++ readOp 22 (.store (.fixed (sourceRegister dest)))
  | .store base offset source =>
      addressProgram base offset ++ callProgram (.fixed (readerPC (Four.slot source).val)) ++
        callProgram (.fixed (readerPC 22 + 3))

@[expose] def Supported : Mov.Instruction → Prop
  | .immediate _ (.address _) => False
  | _ => True

instance (i : Mov.Instruction) : Decidable (Supported i) := by
  cases i with
  | immediate r value => cases value <;> simp [Supported] <;> infer_instance
  | load _ _ _ => exact isTrue trivial
  | store _ _ _ => exact isTrue trivial

theorem kernel_supported : ∀ i ∈ Mov.kernelProgram, Supported i := by decide

@[expose] def compileProgram (program : List Mov.Instruction) : List Header :=
  program.flatMap compileInstruction

@[expose] def kernelProgram : List Header :=
  compileProgram Mov.kernelProgram ++ callProgram (.operand loopField)

theorem reader_length (reader : Nat) : (readerProgram reader).length = 7 := by rfl
theorem guard_length (sense : Bool) : (guardProgram sense).length = 37 := by cases sense <;> rfl

/-- The finite control graph is decoded by quotient/remainder and finite list
lookup. None of its headers depends on the input TM or its future execution. -/
@[expose] def controlHeader (pc : Nat) : Option Header :=
  if pc < 184 then (readerProgram (pc / 8))[pc % 8]?
  else if pc < 224 then (guardProgram false)[pc - 184]?
  else if pc < 264 then (guardProgram true)[pc - 224]?
  else kernelProgram[pc - 264]?

/-- Storage-only template headers have negative PCs: even magnitudes own
nonnegative data fields; odd magnitudes own inactive metadata slots. -/
@[expose] def storageHeader (pc : Int) : Option Header :=
  let magnitude := (-pc).toNat
  if magnitude % 2 = 0 then some (.store (.operand (((magnitude / 2 - 1 : Nat) : Int))))
  else
    let index := (magnitude - 1) / 2
    if 25 ≤ index ∧ index < 38 then some (.store (.operand (metaField index))) else none

@[expose] def headers (pc : Int) : Option (Header × Int) :=
  (if 0 ≤ pc then controlHeader pc.toNat else storageHeader pc).map (fun header => (header, pc + 1))

@[expose] def owner (field : Int) : Int :=
  if 0 ≤ field then -2 * (field + 1)
  else
    let index := (-field - 1).toNat
    if index < 23 then readerPC index + 3
    else if index < 25 then guardPC (decide (index = 24)) + 3
    else -(2 * (index : Int) + 1)

@[expose] def Code (field : Int) : Prop := -38 ≤ field

theorem reader_header (reader index : Nat) (bounded : reader < 23) (small : index < 7) :
    headers (readerPC reader + (index : Int)) =
      ((readerProgram reader)[index]?).map (fun header => (header, readerPC reader + (index : Int) + 1)) := by
  have nonnegative : 0 ≤ readerPC reader + (index : Int) := by simp [readerPC]; omega
  have natural : (readerPC reader + (index : Int)).toNat = 8 * reader + index := by
    simp only [readerPC]
    omega
  have range : 8 * reader + index < 184 := by omega
  have quotient : (8 * reader + index) / 8 = reader := by omega
  have remainder : (8 * reader + index) % 8 = index := by omega
  simp only [headers, nonnegative, ite_true]
  rw [natural]
  simp only [controlHeader, range, ite_true, quotient, remainder]

theorem guard_header (sense : Bool) (index : Nat) (small : index < 37) :
    headers (guardPC sense + (index : Int)) =
      ((guardProgram sense)[index]?).map (fun header => (header, guardPC sense + (index : Int) + 1)) := by
  have nonnegative : 0 ≤ guardPC sense + (index : Int) := by cases sense <;> simp [guardPC] <;> omega
  have natural : (guardPC sense + (index : Int)).toNat = (if sense then 224 else 184) + index := by
    cases sense <;> simp only [guardPC, Bool.false_eq_true, ite_false, ite_true] <;> omega
  simp only [headers, nonnegative, ite_true]
  rw [natural]
  cases sense with
  | false =>
    have first : ¬ 184 + index < 184 := by omega
    have second : 184 + index < 224 := by omega
    have relative : 184 + index - 184 = index := by omega
    simp only [Bool.false_eq_true, ite_false, controlHeader, first, second, ite_true, relative]
  | true =>
    have first : ¬ 224 + index < 184 := by omega
    have second : ¬ 224 + index < 224 := by omega
    have third : 224 + index < 264 := by omega
    have relative : 224 + index - 224 = index := by omega
    simp only [ite_true, controlHeader, first, second, third, ite_false, relative]

theorem data_owner (field : Int) (nonnegative : 0 ≤ field) :
    headers (owner field) = some (.store (.operand field), owner field + 1) := by
  have negative : ¬ 0 ≤ -2 * (field + 1) := by omega
  have magnitude : (-(-2 * (field + 1))).toNat = 2 * (field.toNat + 1) := by omega
  have index : (2 * (field.toNat + 1)) / 2 - 1 = field.toNat := by omega
  simp [owner, nonnegative, headers, negative, storageHeader, magnitude, Int.toNat_of_nonneg nonnegative]

theorem metadata_owner (index : Nat) (bounded : index < 38) :
    headers (owner (metaField index)) =
      some (.store (.operand (metaField index)), owner (metaField index) + 1) := by
  have negative : ¬ 0 ≤ metaField index := by simp [metaField]
  have coordinate : (-metaField index - 1).toNat = index := by simp [metaField]
  by_cases active : index < 23
  · rw [owner, ite_eq_right negative, coordinate, ite_eq_left active]
    simpa [readerProgram, readProgram, stackResetProgram, readerLabel] using
      reader_header index 3 active (by decide)
  · by_cases capture : index < 25
    · have choices : index = 23 ∨ index = 24 := by omega
      rcases choices with equal | equal
      · subst index
        have actual := guard_header false 3 (by decide)
        simpa [owner, metaField, guardPC, guardProgram, readProgram, callProgram, readOp, stackResetProgram,
          captureLabel] using actual
      · subst index
        have actual := guard_header true 3 (by decide)
        simpa [owner, metaField, guardPC, guardProgram, readProgram, callProgram, readOp, stackResetProgram,
          captureLabel] using actual
    · have natNonnegative : 0 ≤ (index : Int) := by omega
      have magnitude : (-(-(2 * (index : Int) + 1))).toNat = 2 * index + 1 := by omega
      have odd : (2 * index + 1) % 2 ≠ 0 := by omega
      have divided : (2 * index + 1 - 1) / 2 = index := by omega
      have low : 25 ≤ index := by omega
      rw [owner, ite_eq_right negative, coordinate, ite_eq_right active, ite_eq_right capture]
      have pcNegative : ¬ 0 ≤ -(2 * (index : Int) + 1) := by omega
      simp only [headers, pcNegative, ite_false, storageHeader, magnitude, odd, divided, low, bounded,
        and_self, ite_true, Option.map_some]

@[expose] def image : Image where
  headers := headers
  templatePC := owner
  codeField := Code
  storageTemplate := by
    intro field code
    refine ⟨owner field + 1, ?_⟩
    by_cases nonnegative : 0 ≤ field
    · exact data_owner field nonnegative
    · have indexBound : (-field - 1).toNat < 38 := by simp only [Code] at code; omega
      have original : metaField ((-field - 1).toNat) = field := by
        change -(((-field - 1).toNat : Int) + 1) = field
        omega
      simpa only [original] using metadata_owner ((-field - 1).toNat) indexBound

theorem meta_is_code (index : Nat) (bounded : index < 38) : image.codeField (metaField index) := by
  change -38 ≤ -((index : Int) + 1)
  omega

theorem data_is_code (field : Int) (nonnegative : 0 ≤ field) : image.codeField field := by
  change -38 ≤ field
  omega

theorem metadata_outside_data (index : Nat) : ¬ codeField dataLayout.data (metaField index) := by
  rintro ⟨field, equal⟩
  simp [dataLayout, fieldAddress, metaField] at equal
  omega

theorem source_register_field (r : Mov.Register) :
    sourceRegister r = Virtual.registerField dataLayout r := by
  simp [sourceRegister, Virtual.registerField, fieldAddress, dataLayout]

theorem storage_owner_injective (first second : Int) (a : image.codeField first)
    (b : image.codeField second) (equal : image.templatePC first = image.templatePC second) : first = second := by
  rcases image.storageTemplate first a with ⟨nextA, headerA⟩
  rcases image.storageTemplate second b with ⟨nextB, headerB⟩
  rw [equal, headerB] at headerA
  have instruction := congrArg Prod.fst (Option.some.inj headerA)
  cases instruction
  rfl

theorem unbounded_storage (bound : Nat) : ∃ field, image.codeField field ∧ (bound : Int) < field := by
  refine ⟨(bound : Int) + 1, data_is_code _ (by omega), ?_⟩
  omega

/-- Placement is now proved for the constructed image, rather than supplied by
the caller. The reader's operand is its single owning storage instruction. -/
theorem reader_placement (reader : Nat) (bounded : reader < 23) :
    ReadRoutinePlacement image (readerLabel reader) (readerPC reader) topField returnField := by
  have h0 := reader_header reader 0 bounded (by decide)
  have h1 := reader_header reader 1 bounded (by decide)
  have h2 := reader_header reader 2 bounded (by decide)
  have h3 := reader_header reader 3 bounded (by decide)
  have h4 := reader_header reader 4 bounded (by decide)
  have h5 := reader_header reader 5 bounded (by decide)
  have h6 := reader_header reader 6 bounded (by decide)
  simp only [readerProgram, readProgram, stackResetProgram, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some] at h0 h1 h2 h3 h4 h5 h6
  refine ⟨?_, h6, ?_⟩
  · simp only [LinearAt, readProgram, stackResetProgram, List.cons_append, List.nil_append, Int.add_assoc]
    exact ⟨h0, h1, h2, h3, h4, h5, trivial⟩
  · have low : ¬ (reader : Int) + 1 ≤ 0 := by omega
    simp [image, owner, readerLabel, metaField, bounded, low]

set_option maxRecDepth 10000 in
theorem kernel_length_bound : kernelProgram.length < 2000 := by decide

theorem terminal_missing : image.headers terminalPC = none := by
  have bound : kernelProgram.length ≤ 999736 := by have := kernel_length_bound; omega
  simp [image, headers, terminalPC, controlHeader, bound]

end SmcTuring.SMC.Concrete

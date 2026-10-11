module
public import SmcTuring.Native.AlignedPool

public section

namespace SmcTuring.Native.RoleInitialization

open ControlImage

inductive Reader where
  | register (register : Dolan.Mov.Register)
  | candidate | boundary | zero | resume | terminal | mask | offsetZero | offsetOne | pointerWord | pointer
  deriving DecidableEq
inductive Field where
  | top | slot | candidate | boundary | zero | resume | terminal | mask | scratch | selected | loop | offsetZero | offsetOne
  deriving DecidableEq

@[expose] def readers : List Reader :=
  (List.ofFn (fun index : Fin 13 => Reader.register (Dolan.Four.registerAt index))) ++
    [.candidate, .boundary, .zero, .resume, .terminal, .mask, .offsetZero, .offsetOne, .pointerWord, .pointer]
@[expose] def fields : List Field :=
  [.top, .slot, .candidate, .boundary, .zero, .resume, .terminal, .mask, .scratch, .selected, .loop, .offsetZero, .offsetOne]
@[expose] def Reader.index : Reader -> Fin 23
  | .register reg => ⟨(Dolan.Four.slot reg).val, by have small := (Dolan.Four.slot reg).isLt; omega⟩
  | .candidate => 13 | .boundary => 14 | .zero => 15 | .resume => 16 | .terminal => 17
  | .mask => 18 | .offsetZero => 19 | .offsetOne => 20 | .pointerWord => 21 | .pointer => 22
@[expose] def Field.index : Field -> Fin 13
  | .top => 0 | .slot => 1 | .candidate => 2 | .boundary => 3 | .zero => 4 | .resume => 5 | .terminal => 6
  | .mask => 7 | .scratch => 8 | .selected => 9 | .loop => 10 | .offsetZero => 11 | .offsetOne => 12

theorem reader_count : readers.length = 23 := rfl
theorem field_count : fields.length = 13 := rfl

theorem reader_at_index (role : Reader) : readers[role.index.val]'(by rw [reader_count]; exact role.index.isLt) = role := by
  cases role with
  | register register => cases register <;> rfl
  | candidate | boundary | zero | resume | terminal | mask | offsetZero | offsetOne | pointerWord | pointer => rfl

theorem field_at_index (role : Field) : fields[role.index.val]'(by rw [field_count]; exact role.index.isLt) = role := by
  cases role <;> rfl

/-- Coordinates are inputs of the two-pass layout: field payloads depend on
these computed addresses, never on future source execution. -/
structure Layout where
  readerStart : Nat
  metadataStart : Nat
  gridBase : Nat
  terminalPC : Nat
  loopPC : Nat

@[expose] def fieldCursor (mode : Mode) (layout : Layout) (role : Field) : Nat :=
  AlignedPool.cursorAt mode .scalar layout.metadataStart role.index.val
@[expose] def fieldPosition (mode : Mode) (layout : Layout) (role : Field) : Nat :=
  AlignedPacking.scalarStart mode (fieldCursor mode layout role) + moffsOperandOffset mode
@[expose] def readerKind (mode : Mode) (layout : Layout) : AlignedPool.Kind :=
  .reader (fieldPosition mode layout .top) (fieldPosition mode layout .slot)
@[expose] def readerCursor (mode : Mode) (layout : Layout) (role : Reader) : Nat :=
  AlignedPool.cursorAt mode (readerKind mode layout) layout.readerStart role.index.val
@[expose] def readerPosition (mode : Mode) (layout : Layout) (role : Reader) : Nat :=
  AlignedPacking.readerStart mode (readerCursor mode layout role)
@[expose] def pointerPosition (mode : Mode) (layout : Layout) : Nat :=
  readerPosition mode layout .pointer + ReaderImage.labelOffset mode

@[expose] def fieldValue (mode : Mode) (layout : Layout) : Field -> Word mode
  | .top => Arithmetic.encodeNat mode (fieldPosition mode layout .slot + mode.wordBytes)
  | .boundary => Arithmetic.encodeNat mode (Native.Layout.heapBase mode layout.gridBase)
  | .terminal => Arithmetic.encodeNat mode layout.terminalPC
  | .loop => Arithmetic.encodeNat mode layout.loopPC
  | .offsetOne => Arithmetic.encodeOffset mode true
  | _ => 0
@[expose] def readerValue (mode : Mode) (layout : Layout) : Reader -> Word mode
  | .register register => SourceData.registerWord mode layout.gridBase register
  | .candidate => Arithmetic.encodeNat mode (fieldPosition mode layout .candidate)
  | .boundary => Arithmetic.encodeNat mode (fieldPosition mode layout .boundary)
  | .zero => Arithmetic.encodeNat mode (fieldPosition mode layout .zero)
  | .resume => Arithmetic.encodeNat mode (fieldPosition mode layout .resume)
  | .terminal => Arithmetic.encodeNat mode (fieldPosition mode layout .terminal)
  | .mask => Arithmetic.encodeNat mode (fieldPosition mode layout .mask)
  | .offsetZero => Arithmetic.encodeNat mode (fieldPosition mode layout .offsetZero)
  | .offsetOne => Arithmetic.encodeNat mode (fieldPosition mode layout .offsetOne)
  | .pointerWord => Arithmetic.encodeNat mode (pointerPosition mode layout)
  | .pointer => SourceData.heapWord mode layout.gridBase (0, false)

@[expose] def readerPayloads (mode : Mode) (layout : Layout) : List (Word mode) := readers.map (readerValue mode layout)
@[expose] def fieldPayloads (mode : Mode) (layout : Layout) : List (Word mode) := fields.map (fieldValue mode layout)
@[expose] def readerPieces (mode : Mode) (layout : Layout) : List (SpacedPacking.Piece mode) :=
  AlignedPool.pool mode (readerKind mode layout) layout.readerStart (readerPayloads mode layout)
@[expose] def fieldPieces (mode : Mode) (layout : Layout) : List (SpacedPacking.Piece mode) :=
  AlignedPool.pool mode .scalar layout.metadataStart (fieldPayloads mode layout)

/-- All 23 literal shared readers initialize the generator's actual role
pointers, including the single shared active load/store operand. -/
theorem reader_initialized (mode : Mode) (layout : Layout) (origin : Nat)
    (leading trailing : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode)
    (location : layout.readerStart = origin + SpacedPacking.size mode leading)
    (fits : forall index, index < 23 -> AlignedPool.Fits mode (readerKind mode layout)
      (AlignedPool.cursorAt mode (readerKind mode layout) layout.readerStart index)) (role : Reader) :
    AlignedPool.Facts mode (readerKind mode layout) (readerCursor mode layout role) origin layout.gridBase
      (readerValue mode layout role) (leading ++ readerPieces mode layout ++ trailing) values := by
  have size : (readerPayloads mode layout).length = 23 := by simp only [readerPayloads, List.length_map, reader_count]
  have actual := AlignedPool.pool_constructed mode (readerKind mode layout) layout.readerStart origin layout.gridBase
    (readerPayloads mode layout) leading trailing values location (fun index inside => fits index (by simpa only [size] using inside))
    role.index.val (by rw [size]; exact role.index.isLt)
  simpa only [readerPieces, readerCursor, readerPayloads, List.getElem_map, reader_at_index] using actual

/-- The 13 storage instructions initialize StackTop, the common return word,
guard constants/scratch, loop target and both Boolean offsets exactly. -/
theorem field_initialized (mode : Mode) (layout : Layout) (origin : Nat)
    (leading trailing : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode)
    (location : layout.metadataStart = origin + SpacedPacking.size mode leading)
    (fits : forall index, index < 13 -> AlignedPool.Fits mode .scalar
      (AlignedPool.cursorAt mode .scalar layout.metadataStart index)) (role : Field) :
    AlignedPool.Facts mode .scalar (fieldCursor mode layout role) origin layout.gridBase
      (fieldValue mode layout role) (leading ++ fieldPieces mode layout ++ trailing) values := by
  have size : (fieldPayloads mode layout).length = 13 := by simp only [fieldPayloads, List.length_map, field_count]
  have actual := AlignedPool.pool_constructed mode .scalar layout.metadataStart origin layout.gridBase
    (fieldPayloads mode layout) leading trailing values location (fun index inside => fits index (by simpa only [size] using inside))
    role.index.val (by rw [size]; exact role.index.isLt)
  simpa only [fieldPieces, fieldCursor, fieldPayloads, List.getElem_map, field_at_index] using actual

end SmcTuring.Native.RoleInitialization

module
public import SmcTuring.Appendix.DivisionRefinement
public import SmcTuring.Appendix.MultiplyPackets
public import SmcTuring.Appendix.DivisionBlocks

public section
namespace SmcTuring.Appendix.DivisionPackets
open DivisionByteCode
abbrev Instruction := DivisionWords.Instruction

@[expose] def literal (instruction : Instruction) (values : Nat → Word) : Form :=
  match instruction with
  | .simple instruction => .common (MultiplyPackets.literal instruction values)
  | .subtractFrom field source => .subtractImmediate (FieldRefinement.address field) (values source)
  | .subtractConstant field value => .subtractImmediate (FieldRefinement.address field) value
  | .addConstant field value => .common (.addImmediate (FieldRefinement.address field) value)
  | .right31 field => .right31 (FieldRefinement.address field)
  | .adcZero field => .adcZero (FieldRefinement.address field)
  | .decrement field => .decrement (FieldRefinement.address field)

theorem literal_current (instruction : Instruction) (state : DivisionByteExecution.State) :
    literal instruction (FieldRefinement.readField state) = DivisionRefinement.translate instruction state := by
  cases instruction with
  | simple instruction => exact congrArg Form.common (MultiplyPackets.literal_current instruction state)
  | _ => rfl

theorem literal_length (instruction : Instruction) (values : Nat → Word) :
    instructionLength (literal instruction values) = DivisionControl.dataLength instruction := by
  cases instruction with
  | simple instruction => exact MultiplyPackets.literal_length instruction values
  | _ => rfl

/-- Body origin, inactive MOV/DEFSTACK owners and the two printed mode flags.
Unused symbolic slots are separate view coordinates and are never code-owned. -/
structure Placement where
  origin : Nat
  inputX : Nat
  inputY : Nat
  result : Nat
  stackInstruction : Nat
  unused : Nat
  mod : Bool
  signed : Bool
  deriving Repr

@[expose] def initialSpan (place : Placement) : Nat :=
  if place.signed then (if place.mod then 280 else 318) else 69
@[expose] def signSpan (place : Placement) : Nat := if place.mod then 51 else 89

/-- Literal owner coordinates read from the original instruction order. -/
@[expose] def fields (place : Placement) : DivisionWords.Fields
  | .x => place.inputX + 6
  | .y => place.inputY + 6
  | .result => place.result + 6
  | .signX => if place.signed then place.origin + (if place.mod then 47 else 62) else place.unused
  | .signY => if place.signed ∧ !place.mod then place.origin + 85 else place.unused + 4
  | .resultSign => if place.signed then place.origin + initialSpan place + 424 else place.unused + 8
  | .xMask => if place.signed then place.origin + signSpan place + 77 else place.unused + 12
  | .xDouble => if place.signed then place.origin + signSpan place + 87 else place.unused + 16
  | .yMask => if place.signed then place.origin + signSpan place + 168 else place.unused + 20
  | .yDouble => if place.signed then place.origin + signSpan place + 178 else place.unused + 24
  | .outputDouble => if place.signed then place.origin + initialSpan place + 434 else place.unused + 28
  | .counter => place.origin + initialSpan place - 4
  | .delta => place.origin + initialSpan place + 92
  | .guardMask => place.origin + initialSpan place + 102
  | .displacement => place.origin + initialSpan place + 113
  | .low => place.origin + initialSpan place + 381
  | .oldLow => place.origin + initialSpan place + 197
  | .oldLow2 => place.origin + initialSpan place + 214
  | .high => place.origin + initialSpan place + 391
  | .divisor => place.origin + initialSpan place + 224
  | .divisor2 => place.origin + initialSpan place + 244
  | .restore => place.origin + initialSpan place + 304
  | .mask => place.origin + initialSpan place + 261
  | .maskComplement => place.origin + initialSpan place + 294
  | .quotientBit => place.origin + initialSpan place + 314

@[expose] def layout (place : Placement) : DivisionBlocks.Layout :=
  { origin := FieldRefinement.address place.origin
    fields := fields place
    mod := place.mod
    signed := place.signed
    pointer := place.stackInstruction + 6
    address := place.stackInstruction + 2
    entryDisplacement := place.origin + initialSpan place + 7
    backDisplacement := place.origin + initialSpan place + 331 }

@[expose] def dataForms (place : Placement) (block : DivisionBlocks.Block) : List Form :=
  (DivisionBlocks.words (layout place) block).map (fun instruction => literal instruction (fun _ => 0x80000000))

@[expose] def tailForms (place : Placement) (displacement : Word) : List Form :=
  [.common (.common (.memory .exchangeStack (FieldRefinement.address (place.stackInstruction + 6)))),
   .common (.common (.callRelative displacement))]

@[expose] def restoreForms (place : Placement) : List Form :=
  (ByteControl.restoreForms (FieldRefinement.address (place.stackInstruction + 6))
    (FieldRefinement.address (place.stackInstruction + 2))).map (fun form => .common (.common form))

/-- Original order after M06/M11's minimal substitutions; static packets are
emitted once. This list is an image, not an assumed future execution trace. -/
@[expose] def packets (place : Placement) : List Form :=
  dataForms place .initial ++ tailForms place 0 ++ restoreForms place ++
    dataForms place .guard ++ tailForms place 0 ++ restoreForms place ++
    dataForms place .body ++ tailForms place (DivisionBlocks.backDelta (layout place)) ++
    restoreForms place ++ dataForms place .finish

@[expose] def inactiveOwners (place : Placement) : List (Nat × Form) :=
  [(place.inputX, .common (.common (.immediate .store (FieldRefinement.address (place.inputX + 6)) 0))),
   (place.inputY, .common (.common (.immediate .store (FieldRefinement.address (place.inputY + 6)) 0))),
   (place.result, .common (.common (.immediate .store (FieldRefinement.address (place.result + 6)) 0))),
   (place.stackInstruction, .common (.common (.immediate .store
     (FieldRefinement.address (place.stackInstruction + 6)) (FieldRefinement.address (place.stackInstruction + 6)))))]

@[expose] def span (forms : List Form) : Nat := (forms.map instructionLength).sum
@[expose] def positioned : Nat → List Form → List (Nat × Form)
  | _, [] => []
  | pc, form :: rest => (pc, form) :: positioned (pc + instructionLength form) rest

theorem data_span (place : Placement) (block : DivisionBlocks.Block) :
    span (dataForms place block) = DivisionControl.span (DivisionBlocks.words (layout place) block) := by
  simp only [span, dataForms, List.map_map, Function.comp_def, literal_length, DivisionControl.span]

theorem tail_span (place : Placement) (displacement : Word) : span (tailForms place displacement) = 11 := rfl

theorem restore_span (place : Placement) : span (restoreForms place) = 30 := rfl

theorem span_append (first second : List Form) : span (first ++ second) = span first + span second := by
  simp [span]

theorem packet_span (place : Placement) : span (packets place) =
    initialSpan place + 365 + (if place.signed then 73 else 30) := by
  have lengths := DivisionBlocks.literal_lengths (layout place)
  simp only [packets, span_append, data_span, tail_span, restore_span]
  rw [lengths.1, lengths.2.1, lengths.2.2.1, lengths.2.2.2]
  change initialSpan place + 11 + 30 + 65 + 11 + 30 + 177 + 11 + 30 +
    (if place.signed then 73 else 30) = initialSpan place + 365 +
      (if place.signed then 73 else 30)
  omega

theorem packet_count (place : Placement) : (packets place).length =
    if place.signed then (if place.mod then 98 else 103) else 65 := by
  cases signed : place.signed <;> cases mod : place.mod <;>
    simp [packets, dataForms, layout, DivisionBlocks.words, DivisionWords.initializeData,
      DivisionWords.signPrefix, DivisionWords.sample, DivisionWords.normalize, DivisionWords.copy,
      MultiplyWords.copyProgram, DivisionGuard.program, MultiplyWords.guard,
      DivisionWords.body, DivisionWords.finishData, tailForms, restoreForms,
      ByteControl.restoreForms, signed, mod]

theorem inactive_count (place : Placement) : (inactiveOwners place).length = 4 := rfl

theorem inactive_span (place : Placement) : span ((inactiveOwners place).map Prod.snd) = 40 := rfl

end SmcTuring.Appendix.DivisionPackets

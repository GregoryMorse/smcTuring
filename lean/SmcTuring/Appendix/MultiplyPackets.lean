module
public import SmcTuring.Appendix.MultiplyRefinement
public import SmcTuring.Appendix.MultiplyBlocks
public import SmcTuring.Appendix.ByteControl

public section
namespace SmcTuring.Appendix.MultiplyPackets

open MultiplyByteCode
abbrev Instruction := MultiplyWords.Instruction

/-- Static form with a field-value function. Current translations instantiate
this function with actual DWORD loads; initial packets use printed placeholders. -/
@[expose] def literal (instruction : Instruction) (values : Nat → Word) : Form :=
  match instruction with
  | .selected instruction => .common (match instruction with
    | .store field value => .immediate .store (FieldRefinement.address field) value
    | .exchange field => .memory .exchangeAcc (FieldRefinement.address field)
    | .xorConstant field value => .immediate .bitXor (FieldRefinement.address field) value
    | .subtractAcc field => .memory .subtractAcc (FieldRefinement.address field)
    | .addAcc field => .memory .addAcc (FieldRefinement.address field)
    | .negate field => .memory .negate (FieldRefinement.address field)
    | .sbbZero field => .memory .sbbZero (FieldRefinement.address field)
    | .complement field => .memory .complement (FieldRefinement.address field)
    | .andField field source => .immediate .bitAnd (FieldRefinement.address field) (values source)
    | .xorField field source => .immediate .bitXor (FieldRefinement.address field) (values source))
  | .storeAcc field => .common (.storeAcc (FieldRefinement.address field))
  | .andAcc field => .andAcc (FieldRefinement.address field)
  | .selfStore field => .common (.immediate .store (FieldRefinement.address field) (values field))
  | .copyFrom field source => .common (.immediate .store (FieldRefinement.address field) (values source))
  | .addFrom field source => .addImmediate (FieldRefinement.address field) (values source)
  | .shiftLeft field => .shiftLeft (FieldRefinement.address field)
  | .shiftRight field => .shiftRight (FieldRefinement.address field)

theorem literal_current (instruction : Instruction) (state : MultiplyByteExecution.State) :
    literal instruction (FieldRefinement.readField state) = MultiplyRefinement.translate instruction state := by
  cases instruction with
  | selected instruction => cases instruction <;> rfl
  | _ => rfl

theorem literal_length (instruction : Instruction) (values : Nat → Word) :
    instructionLength (literal instruction values) = MultiplyControl.dataLength instruction := by
  cases instruction with
  | selected instruction => cases instruction <;> rfl
  | _ => rfl

/-- Contiguous pure body and independently placed inactive MOV/DEFSTACK owners.
Capacity and separation of complete byte windows remain explicit layout gates. -/
structure Placement where
  origin : Nat
  inputX : Nat
  inputY : Nat
  result : Nat
  stackInstruction : Nat
  deriving Repr

@[expose] def fields (place : Placement) : MultiplyWords.Fields
  | .x => place.inputX + 6
  | .y => place.inputY + 6
  | .result => place.result + 6
  | .factor => place.origin + 295
  | .multiplier => place.origin + 311
  | .total => place.origin + 378
  | .delta => place.origin + 136
  | .mask => place.origin + 146
  | .displacement => place.origin + 157
  | .bit => place.origin + 252
  | .addMask => place.origin + 275
  | .addend => place.origin + 285

@[expose] def layout (place : Placement) : MultiplyBlocks.Layout :=
  { origin := FieldRefinement.address place.origin
    fields := fields place
    pointer := place.stackInstruction + 6
    address := place.stackInstruction + 2
    entryDisplacement := place.origin + 51
    backDisplacement := place.origin + 328 }

@[expose] def dataForms (place : Placement) (block : MultiplyBlocks.Block) : List Form :=
  (MultiplyBlocks.words (layout place) block).map (fun instruction => literal instruction (fun _ => 0x80000000))

@[expose] def tailForms (place : Placement) (displacement : Word) : List Form :=
  [.common (.memory .exchangeStack (FieldRefinement.address (place.stackInstruction + 6))),
   .common (.callRelative displacement)]

@[expose] def restoreForms (place : Placement) : List Form :=
  (ByteControl.restoreForms (FieldRefinement.address (place.stackInstruction + 6))
    (FieldRefinement.address (place.stackInstruction + 2))).map Form.common

/-- Exact printed order, with M07's corrected delta and continuation geometry.
This emits initial bytes; it is not a preselected execution trace. -/
@[expose] def packets (place : Placement) : List Form :=
  dataForms place .initial ++ tailForms place 0 ++ restoreForms place ++
    dataForms place .guard ++ tailForms place 0 ++ restoreForms place ++
    dataForms place .body ++ tailForms place (MultiplyBlocks.backDelta (layout place)) ++
    restoreForms place ++ dataForms place .finish

/-- Inactive owner instructions from the printed input/result/DEFSTACK
layout. Their operand bytes are code fields even though these owners are skipped. -/
@[expose] def inactiveOwners (place : Placement) : List (Nat × Form) :=
  [(place.inputX, .common (.immediate .store (FieldRefinement.address (place.inputX + 6)) 0)),
   (place.inputY, .common (.immediate .store (FieldRefinement.address (place.inputY + 6)) 0)),
   (place.result, .common (.immediate .store (FieldRefinement.address (place.result + 6)) 0)),
   (place.stackInstruction, .common (.immediate .store
     (FieldRefinement.address (place.stackInstruction + 6))
     (FieldRefinement.address (place.stackInstruction + 6))))]

@[expose] def span (forms : List Form) : Nat := (forms.map instructionLength).sum

@[expose] def positioned : Nat → List Form → List (Nat × Form)
  | _, [] => []
  | pc, form :: rest => (pc, form) :: positioned (pc + instructionLength form) rest

theorem data_lengths (place : Placement) :
    ([MultiplyBlocks.Block.initial, .guard, .body, .finish].map
      (fun block => (dataForms place block).map instructionLength)) =
      [[10,6,5,6,6,5,6], [10,6,7,6,6,10,10,10],
       [10,6,6,6,6,5,6,10,10,6,7,10,10,10,6,10,6], [10,10]] := rfl

theorem tail_span (place : Placement) (displacement : Word) : span (tailForms place displacement) = 11 := rfl

theorem restore_span (place : Placement) : span (restoreForms place) = 30 := rfl

theorem packet_count (place : Placement) : (packets place).length = 55 := rfl

theorem data_lengths_block (place : Placement) (block : MultiplyBlocks.Block) :
    (dataForms place block).map instructionLength = match block with
      | .initial => [10,6,5,6,6,5,6]
      | .guard => [10,6,7,6,6,10,10,10]
      | .body => [10,6,6,6,6,5,6,10,10,6,7,10,10,10,6,10,6]
      | .finish => [10,10] := by cases block <;> rfl

theorem packet_lengths (place : Placement) :
    (packets place).map instructionLength = [10, 6, 5, 6, 6, 5, 6, 6, 5, 6, 7, 6, 5, 6, 10, 6, 7, 6, 6, 10, 10, 10, 6, 5, 6, 7, 6, 5, 6, 10, 6, 6, 6, 6, 5, 6, 10, 10, 6, 7, 10, 10, 10, 6, 10, 6, 6, 5, 6, 7, 6, 5, 6, 10, 10] := by
  simp only [packets, List.map_append, data_lengths_block, tailForms, restoreForms,
    ByteControl.restoreForms, List.map_cons, List.map_nil, instructionLength,
    ByteCode.instructionLength, ByteCode.MemoryOp.trailer, List.length_cons,
    List.length_nil, Nat.reduceAdd, List.cons_append, List.nil_append]

theorem packet_span (place : Placement) : span (packets place) = 382 := by
  rw [span, packet_lengths]
  rfl

@[expose] def offsets : Nat → List Nat → List Nat
  | _, [] => []
  | pc, length :: rest => pc :: offsets (pc + length) rest

theorem positioned_offsets (pc : Nat) (forms : List Form) :
    (positioned pc forms).map Prod.fst = offsets pc (forms.map instructionLength) := by
  induction forms generalizing pc with
  | nil => rfl
  | cons form rest ih => simp only [positioned, List.map_cons, offsets, ih]

theorem packet_offsets (place : Placement) :
    (positioned 0 (packets place)).map Prod.fst = [0, 10, 16, 21, 27, 33, 38, 44, 50, 55, 61, 68, 74, 79, 85, 95, 101, 108, 114, 120, 130, 140, 150, 156, 161, 167, 174, 180, 185, 191, 201, 207, 213, 219, 225, 230, 236, 246, 256, 262, 269, 279, 289, 299, 305, 315, 321, 327, 332, 338, 345, 351, 356, 362, 372] := by
  rw [positioned_offsets, packet_lengths]
  rfl

theorem owner_coordinates (place : Placement) :
    [fields place .delta, fields place .mask, fields place .displacement,
     fields place .bit, fields place .addMask, fields place .addend,
     fields place .factor, fields place .multiplier, fields place .total] =
      [136,146,157,252,275,285,295,311,378].map (place.origin + ·) := rfl

theorem stack_alias (place : Placement) : (layout place).address + 4 = (layout place).pointer := by
  simp only [layout]

theorem inactive_count (place : Placement) : (inactiveOwners place).length = 4 := rfl

theorem inactive_span (place : Placement) : span ((inactiveOwners place).map Prod.snd) = 40 := rfl

end SmcTuring.Appendix.MultiplyPackets

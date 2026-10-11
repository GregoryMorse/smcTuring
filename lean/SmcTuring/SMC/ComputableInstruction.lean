module
public import SmcTuring.SMC.ComputableState

public section

namespace SmcTuring.SMC.Effective

open Dolan.Encoding

/-- A finite instruction descriptor: an opcode and one canonical signed word. -/
abbrev InstructionCode := Prod Nat Nat

@[expose] def instructionArg : Instruction -> Int
  | .exchange field | .store field | .add field | .subtract field
  | .subtractBorrowZero field | .bitXor field | .bitAnd field
  | .exchangeStack field | .storeStack field | .call field => field

@[expose] def instructionCode : Instruction -> InstructionCode
  | .exchange field => (0, zigzag field)
  | .store field => (1, zigzag field)
  | .add field => (2, zigzag field)
  | .subtract field => (3, zigzag field)
  | .subtractBorrowZero field => (4, zigzag field)
  | .bitXor field => (5, zigzag field)
  | .bitAnd field => (6, zigzag field)
  | .exchangeStack field => (7, zigzag field)
  | .storeStack field => (8, zigzag field)
  | .call target => (9, zigzag target)

@[expose] def decodeInstruction (code : InstructionCode) : Option Instruction :=
  if 10 <= code.1 then none else
  if code.1 = 0 then some (.exchange (unzigzag code.2)) else
  if code.1 = 1 then some (.store (unzigzag code.2)) else
  if code.1 = 2 then some (.add (unzigzag code.2)) else
  if code.1 = 3 then some (.subtract (unzigzag code.2)) else
  if code.1 = 4 then some (.subtractBorrowZero (unzigzag code.2)) else
  if code.1 = 5 then some (.bitXor (unzigzag code.2)) else
  if code.1 = 6 then some (.bitAnd (unzigzag code.2)) else
  if code.1 = 7 then some (.exchangeStack (unzigzag code.2)) else
  if code.1 = 8 then some (.storeStack (unzigzag code.2)) else
  some (.call (unzigzag code.2))

theorem instruction_code_arg (instruction : Instruction) :
    (instructionCode instruction).2 = zigzag (instructionArg instruction) := by cases instruction <;> rfl

theorem instruction_code_valid (instruction : Instruction) : (instructionCode instruction).1 < 10 := by
  cases instruction <;> simp [instructionCode]

theorem decode_instruction_code (instruction : Instruction) : decodeInstruction (instructionCode instruction) = some instruction := by
  cases instruction <;> simp [decodeInstruction, instructionCode, unzigzag_zigzag]

/-- All state updates take finite coded data. The fallback word is computed
separately by the fixed initial-memory algorithm; it is not a memory oracle. -/
@[expose] def executeInstructionCode (wordBytes next fallback : Nat) (code : InstructionCode) (s : StateCode) : Option StateCode :=
  let field := code.2
  let word := read fallback s.2.2.2.2 field
  let acc := s.1
  let stack := s.2.1
  let carry := s.2.2.2.1
  let journal := s.2.2.2.2
  if 10 <= code.1 then none else
  if code.1 = 0 then some (word, stack, next, carry, push field acc journal) else
  if code.1 = 1 then some (acc, stack, next, carry, push field acc journal) else
  if code.1 = 2 then some (acc, stack, next, false, push field (addCode word acc) journal) else
  if code.1 = 3 then some (acc, stack, next, lessCode word acc, push field (subtractCode word acc) journal) else
  if code.1 = 4 then some (acc, stack, next, lessCode word (borrowCode carry), push field (subtractBorrowCode word carry) journal) else
  if code.1 = 5 then some (acc, stack, next, false, push field (xorCode word acc) journal) else
  if code.1 = 6 then some (acc, stack, next, false, push field (andCode word acc) journal) else
  if code.1 = 7 then some (acc, word, next, carry, push field stack journal) else
  if code.1 = 8 then some (acc, stack, next, carry, push field stack journal) else
  let newStack := subtractCode stack wordBytes
  some (acc, newStack, field, carry, push newStack next journal)

theorem execute_instruction_code_correct (wordBytes next : Int) (initial : Int -> Int) (instruction : Instruction) (s : Finite.State) :
    executeInstructionCode (zigzag wordBytes) (zigzag next) (zigzag (initial (instructionArg instruction)))
      (instructionCode instruction) (stateCode s) = some (stateCode (Finite.execute wordBytes initial instruction next s)) := by
  cases instruction <;>
    simp [executeInstructionCode, instructionCode, instructionArg, stateCode, Finite.execute,
      read_correct, push_correct, add_correct, subtract_correct, subtract_borrow_correct,
      less_correct, borrow_correct, xor_correct, and_correct]

theorem execute_invalid_code (wordBytes next fallback : Nat) (code : InstructionCode) (s : StateCode)
    (invalid : 10 <= code.1) : executeInstructionCode wordBytes next fallback code s = none := by
  simp only [executeInstructionCode, invalid, ite_true]

abbrev ExecuteInputs := Prod Nat (Prod Nat (Prod Nat (Prod InstructionCode StateCode)))

/-- A uniform primitive-recursion certificate for all ten instruction effects,
including the code-backed CALL stack write. No function-valued argument occurs. -/
theorem execute_instruction_code_primrec : Primrec (fun input : ExecuteInputs =>
    executeInstructionCode input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2) := by
  have bytesField : Primrec (fun input : ExecuteInputs => input.1) := Primrec.fst
  have nextField : Primrec (fun input : ExecuteInputs => input.2.1) := Primrec.fst.comp Primrec.snd
  have fallbackField : Primrec (fun input : ExecuteInputs => input.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have instructionField : Primrec (fun input : ExecuteInputs => input.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have stateField : Primrec (fun input : ExecuteInputs => input.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have tagField := Primrec.fst.comp instructionField
  have addressField := Primrec.snd.comp instructionField
  have accField := Primrec.fst.comp stateField
  have stackField := Primrec.fst.comp (Primrec.snd.comp stateField)
  have carryField := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp stateField)))
  have journalField := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp stateField)))
  have wordField := read_primrec.comp (Primrec.pair (Primrec.pair fallbackField journalField) addressField)
  have eqTag (tag : Nat) : PrimrecPred (fun input : ExecuteInputs => input.2.2.2.1.1 = tag) :=
    Primrec.eq.comp tagField (Primrec.const tag)
  have put {field datum : ExecuteInputs -> Nat} (hf : Primrec field) (hv : Primrec datum) :
      Primrec (fun input => push (field input) (datum input) input.2.2.2.2.2.2.2.2) :=
    (push_primrec.comp (Primrec.pair (Primrec.pair hf hv) journalField)).of_eq fun input => by rfl
  have build {acc stack pc : ExecuteInputs -> Nat} {carry : ExecuteInputs -> Bool} {journal : ExecuteInputs -> Journal}
      (ha : Primrec acc) (hs : Primrec stack) (hp : Primrec pc) (hc : Primrec carry) (hj : Primrec journal) :
      Primrec (fun input => some (acc input, stack input, pc input, carry input, journal input)) :=
    Primrec.option_some.comp (Primrec.pair ha (Primrec.pair hs (Primrec.pair hp (Primrec.pair hc hj))))
  have newStack := subtract_primrec.comp stackField bytesField
  exact Primrec.ite (Primrec.nat_le.comp (Primrec.const 10) tagField) (Primrec.const none)
    (Primrec.ite (eqTag 0) (build wordField stackField nextField carryField (put addressField accField))
      (Primrec.ite (eqTag 1) (build accField stackField nextField carryField (put addressField accField))
      (Primrec.ite (eqTag 2) (build accField stackField nextField (Primrec.const false) (put addressField (add_primrec.comp wordField accField)))
      (Primrec.ite (eqTag 3) (build accField stackField nextField (less_primrec.comp wordField accField) (put addressField (subtract_primrec.comp wordField accField)))
      (Primrec.ite (eqTag 4) (build accField stackField nextField (less_primrec.comp wordField (borrow_primrec.comp carryField)) (put addressField (subtract_borrow_primrec.comp wordField carryField)))
      (Primrec.ite (eqTag 5) (build accField stackField nextField (Primrec.const false) (put addressField (xor_primrec.comp wordField accField)))
      (Primrec.ite (eqTag 6) (build accField stackField nextField (Primrec.const false) (put addressField (and_primrec.comp wordField accField)))
      (Primrec.ite (eqTag 7) (build accField wordField nextField carryField (put addressField stackField))
      (Primrec.ite (eqTag 8) (build accField stackField nextField carryField (put addressField stackField))
      (build accField newStack addressField carryField (put newStack nextField)))))))))))

end SmcTuring.SMC.Effective

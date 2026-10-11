module
public import SmcTuring.SMC.ComputableInstruction

public section

namespace SmcTuring.SMC.Effective

open Dolan.Encoding

@[expose] def addressArg : Address -> Int
  | .fixed word | .operand word => word
  | .accumulator => 0

@[expose] def addressCode : Address -> InstructionCode
  | .fixed word => (0, zigzag word)
  | .accumulator => (1, 0)
  | .operand field => (2, zigzag field)

@[expose] def resolveAddressCode (fallback : Nat) (code : InstructionCode) (s : StateCode) : Option Nat :=
  if code.1 = 0 then some code.2 else
  if code.1 = 1 then some s.1 else
  if code.1 = 2 then some (read fallback s.2.2.2.2 code.2) else none

theorem resolve_address_code_correct (initial : Int -> Int) (address : Address) (s : Finite.State) :
    resolveAddressCode (zigzag (initial (addressArg address))) (addressCode address) (stateCode s) =
      some (zigzag (Finite.eval initial address s)) := by
  cases address <;> simp [resolveAddressCode, addressArg, addressCode, stateCode, Finite.eval, read_correct]

abbrev AddressInputs := Prod Nat (Prod InstructionCode StateCode)

theorem resolve_address_code_primrec : Primrec (fun input : AddressInputs =>
    resolveAddressCode input.1 input.2.1 input.2.2) := by
  have fallbackField : Primrec (fun input : AddressInputs => input.1) := Primrec.fst
  have codeField : Primrec (fun input : AddressInputs => input.2.1) := Primrec.fst.comp Primrec.snd
  have stateField : Primrec (fun input : AddressInputs => input.2.2) := Primrec.snd.comp Primrec.snd
  have tagField := Primrec.fst.comp codeField
  have argumentField := Primrec.snd.comp codeField
  have accumulatorField := Primrec.fst.comp stateField
  have journalField := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp stateField)))
  have readField := read_primrec.comp (Primrec.pair (Primrec.pair fallbackField journalField) argumentField)
  have tagEq (tag : Nat) : PrimrecPred (fun input : AddressInputs => input.2.1.1 = tag) :=
    Primrec.eq.comp tagField (Primrec.const tag)
  exact Primrec.ite (tagEq 0) (Primrec.option_some.comp argumentField)
    (Primrec.ite (tagEq 1) (Primrec.option_some.comp accumulatorField)
      (Primrec.ite (tagEq 2) (Primrec.option_some.comp readField) (Primrec.const none)))

theorem resolve_invalid_address (fallback : Nat) (code : InstructionCode) (s : StateCode)
    (invalid : 3 <= code.1) : resolveAddressCode fallback code s = none := by
  have zero : code.1 ≠ 0 := by omega
  have one : code.1 ≠ 1 := by omega
  have two : code.1 ≠ 2 := by omega
  simp only [resolveAddressCode, zero, one, two, ite_false]

abbrev HeaderCode := Prod Nat InstructionCode

@[expose] def headerArg : Header -> Int
  | .exchange address | .store address | .call address => addressArg address
  | .add field | .subtract field | .subtractBorrowZero field | .bitXor field
  | .bitAnd field | .exchangeStack field | .storeStack field => field

@[expose] def headerCode : Header -> HeaderCode
  | .exchange address => (0, addressCode address)
  | .store address => (1, addressCode address)
  | .add field => (2, addressCode (.fixed field))
  | .subtract field => (3, addressCode (.fixed field))
  | .subtractBorrowZero field => (4, addressCode (.fixed field))
  | .bitXor field => (5, addressCode (.fixed field))
  | .bitAnd field => (6, addressCode (.fixed field))
  | .exchangeStack field => (7, addressCode (.fixed field))
  | .storeStack field => (8, addressCode (.fixed field))
  | .call address => (9, addressCode address)

@[expose] def decodeHeaderCode (fallback : Nat) (code : HeaderCode) (s : StateCode) : Option InstructionCode :=
  if code.1 < 10 then (resolveAddressCode fallback code.2 s).map (fun word => (code.1, word)) else none

theorem header_code_valid (header : Header) : (headerCode header).1 < 10 := by
  cases header <;> simp [headerCode]

theorem decode_header_code_correct (initial : Int -> Int) (header : Header) (s : Finite.State) :
    decodeHeaderCode (zigzag (initial (headerArg header))) (headerCode header) (stateCode s) =
      some (instructionCode (Finite.decode initial header s)) := by
  cases header <;>
    simp [decodeHeaderCode, headerCode, headerArg, Finite.decode, instructionCode, resolve_address_code_correct] <;>
    simp [resolveAddressCode, addressCode]

abbrev HeaderInputs := Prod Nat (Prod HeaderCode StateCode)

theorem decode_header_code_primrec : Primrec (fun input : HeaderInputs =>
    decodeHeaderCode input.1 input.2.1 input.2.2) := by
  have codeField : Primrec (fun input : HeaderInputs => input.2.1) := Primrec.fst.comp Primrec.snd
  have stateField : Primrec (fun input : HeaderInputs => input.2.2) := Primrec.snd.comp Primrec.snd
  have tagField := Primrec.fst.comp codeField
  have addressField := Primrec.snd.comp codeField
  have resolved := resolve_address_code_primrec.comp (Primrec.pair Primrec.fst (Primrec.pair addressField stateField))
  have paired : Primrec (fun input : HeaderInputs =>
      (resolveAddressCode input.1 input.2.1.2 input.2.2).map (fun word => (input.2.1.1, word))) :=
    Primrec.option_map resolved (Primrec.pair (tagField.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.ite (Primrec.nat_lt.comp tagField (Primrec.const 10)) paired (Primrec.const none)

theorem decode_invalid_header (fallback : Nat) (code : HeaderCode) (s : StateCode)
    (invalid : 10 <= code.1) : decodeHeaderCode fallback code s = none := by
  have outside : Not (code.1 < 10) := by omega
  simp only [decodeHeaderCode, outside, ite_false]

end SmcTuring.SMC.Effective

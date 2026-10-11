module
public import SmcTuring.SMC.ComputableBitwise

public section

namespace SmcTuring.SMC.Effective

open Dolan.Encoding

/-- A finite, canonically encodable execution state. -/
abbrev StateCode := Nat × Nat × Nat × Bool × Journal

@[expose] def stateCode (s : Finite.State) : StateCode :=
  (zigzag s.acc, zigzag s.stack, zigzag s.pc, s.carry, journalCode s.changes)

@[expose] def decodeState (s : StateCode) : Finite.State :=
  { acc := unzigzag s.1, stack := unzigzag s.2.1, pc := unzigzag s.2.2.1,
    carry := s.2.2.2.1, changes := journalDecode s.2.2.2.2 }

theorem decode_state_code (s : Finite.State) : decodeState (stateCode s) = s := by
  cases s
  simp only [decodeState, stateCode, unzigzag_zigzag, journal_decode_code]

theorem state_code_decode (s : StateCode) : stateCode (decodeState s) = s := by
  rcases s with ⟨acc, stack, pc, carry, journal⟩
  simp only [decodeState, stateCode, zigzag_unzigzag, journal_code_decode]

@[expose] def packState (s : StateCode) : List Nat :=
  s.1 :: s.2.1 :: s.2.2.1 :: borrowCode s.2.2.2.1 :: flatten s.2.2.2.2

theorem pack_state_correct (s : Finite.State) : packState (stateCode s) = Finite.serializeNat s := by
  cases s with
  | mk acc stack pc carry changes =>
    cases carry <;> simp [packState, stateCode, Finite.serializeNat, Finite.serialize, borrowCode, flatten_correct, zigzag]

theorem pack_state_primrec : Primrec packState := by
  have stackField := Primrec.fst.comp (Primrec.snd (α := Nat) (β := Nat × Nat × Bool × Journal))
  have pcField := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd (α := Nat) (β := Nat × Nat × Bool × Journal)))
  have flagField := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd (α := Nat) (β := Nat × Nat × Bool × Journal))))
  have journalField := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd (α := Nat) (β := Nat × Nat × Bool × Journal))))
  exact Primrec.list_cons.comp Primrec.fst
    (Primrec.list_cons.comp stackField (Primrec.list_cons.comp pcField
      (Primrec.list_cons.comp (borrow_primrec.comp flagField) (flatten_primrec.comp journalField))))

/-- Read a flat address/value list from the right. A pending value is paired
with the preceding address; a leftover pending value identifies odd length. -/
@[expose] def pairStep (word : Nat) (journalState : Option Nat × Journal) : Option Nat × Journal :=
  match journalState.1 with
  | none => (some word, journalState.2)
  | some pending => (none, (word, pending) :: journalState.2)

@[expose] def pairFold (words : List Nat) : Option Nat × Journal :=
  words.foldr pairStep (none, [])

@[expose] def unflatten (words : List Nat) : Option Journal :=
  match (pairFold words).1 with
  | none => some (pairFold words).2
  | some _ => none

theorem pair_step_primrec : Primrec₂ pairStep := by
  exact (Primrec.option_casesOn (Primrec.fst.comp Primrec.snd)
    (Primrec.pair (Primrec.option_some.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.pair (Primrec.const none)
      (Primrec.list_cons.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to₂).of_eq
      fun input => by unfold pairStep; cases input.2.1 <;> rfl

theorem pair_fold_primrec : Primrec pairFold :=
  Primrec.list_foldr Primrec.id (Primrec.const (none, []))
    (pair_step_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem unflatten_primrec : Primrec unflatten := by
  exact (Primrec.option_casesOn (Primrec.fst.comp pair_fold_primrec)
    (Primrec.option_some.comp (Primrec.snd.comp pair_fold_primrec)) (Primrec.const none).to₂).of_eq
      fun words => by unfold unflatten; cases (pairFold words).1 <;> rfl

theorem pair_fold_flatten (journal : Journal) : pairFold (flatten journal) = (none, journal) := by
  induction journal with
  | nil => rfl
  | cons entry rest ih =>
    change pairStep entry.1 (pairStep entry.2 (pairFold (flatten rest))) = (none, entry :: rest)
    rw [ih]
    rfl

theorem unflatten_flatten (journal : Journal) : unflatten (flatten journal) = some journal := by
  unfold unflatten
  rw [pair_fold_flatten]

theorem unflatten_two (field datum : Nat) (rest : List Nat) :
    unflatten (field :: datum :: rest) = (unflatten rest).map ((field, datum) :: ·) := by
  unfold unflatten
  change (match (pairStep field (pairStep datum (pairFold rest))).1 with
    | none => some (pairStep field (pairStep datum (pairFold rest))).2
    | some _ => none) = _
  cases pending : (pairFold rest).1 <;> simp [pairStep, pending]

theorem unflatten_correct (words : List Nat) :
    (unflatten words).map journalDecode = Finite.decodeChanges (words.map unzigzag) := by
  match words with
  | [] => rfl
  | [_] => rfl
  | field :: datum :: rest =>
    rw [unflatten_two]
    simp only [List.map_cons, Finite.decodeChanges]
    rw [← unflatten_correct rest]
    simp only [Option.map_map, Function.comp_def, journalDecode, List.map_cons]
termination_by words.length

@[expose] def wordAt (words : List Nat) (index : Nat) : Nat := words[index]?.getD 0

theorem word_at_primrec : Primrec₂ wordAt :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd) (Primrec.const 0)

@[expose] def recordState (words : List Nat) (carry : Bool) (journal : Journal) : StateCode :=
  (wordAt words 0, wordAt words 1, wordAt words 2, carry, journal)

theorem record_state_primrec (carry : Bool) : Primrec₂ (fun words journal => recordState words carry journal) := by
  exact Primrec.pair (word_at_primrec.comp Primrec.fst (Primrec.const 0))
    (Primrec.pair (word_at_primrec.comp Primrec.fst (Primrec.const 1))
      (Primrec.pair (word_at_primrec.comp Primrec.fst (Primrec.const 2))
        (Primrec.pair (Primrec.const carry) Primrec.snd)))

@[expose] def parseState (words : List Nat) : Option StateCode :=
  if words.length < 4 then none else
  if wordAt words 3 = 0 then (unflatten (words.drop 4)).map (recordState words false)
  else if wordAt words 3 = 2 then (unflatten (words.drop 4)).map (recordState words true)
  else none

theorem parse_state_primrec : Primrec parseState := by
  have journal := unflatten_primrec.comp (Primrec.list_drop.comp (Primrec.const 4) Primrec.id)
  exact Primrec.ite (Primrec.nat_lt.comp Primrec.list_length (Primrec.const 4)) (Primrec.const none)
    (Primrec.ite (Primrec.eq.comp (word_at_primrec.comp Primrec.id (Primrec.const 3)) (Primrec.const 0))
      (Primrec.option_map journal (record_state_primrec false))
      (Primrec.ite (Primrec.eq.comp (word_at_primrec.comp Primrec.id (Primrec.const 3)) (Primrec.const 2))
        (Primrec.option_map journal (record_state_primrec true)) (Primrec.const none)))

theorem parse_pack_state (s : StateCode) : parseState (packState s) = some s := by
  rcases s with ⟨acc, stack, pc, carry, journal⟩
  cases carry <;> simp [parseState, packState, wordAt, borrowCode, unflatten_flatten, recordState]

theorem parse_serialized_state (s : Finite.State) :
    (parseState (Finite.serializeNat s)).map decodeState = some s := by
  rw [← pack_state_correct, parse_pack_state, Option.map_some, decode_state_code]

end SmcTuring.SMC.Effective

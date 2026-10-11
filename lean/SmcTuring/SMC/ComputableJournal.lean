module
public import Mathlib.Computability.Primrec.List
public import SmcTuring.SMC.FiniteSerialization

public section

namespace SmcTuring.SMC.Effective

abbrev Journal := List (Nat × Nat)

@[expose] def journalCode (changes : List (Int × Int)) : Journal :=
  changes.map fun entry => (Dolan.Encoding.zigzag entry.1, Dolan.Encoding.zigzag entry.2)

@[expose] def journalDecode (changes : Journal) : List (Int × Int) :=
  changes.map fun entry => (Dolan.Encoding.unzigzag entry.1, Dolan.Encoding.unzigzag entry.2)

/-- The fallback is a finite word computed by the separate initial-word
algorithm. The memory operation itself has no function-valued input. -/
@[expose] def read (fallback : Nat) (changes : Journal) (field : Nat) : Nat :=
  (changes.lookup field).getD fallback

@[expose] def push (field datum : Nat) (changes : Journal) : Journal := (field, datum) :: changes

@[expose] def flatten (changes : Journal) : List Nat := changes.flatMap fun entry => [entry.1, entry.2]

theorem zigzag_unzigzag (word : Nat) : Dolan.Encoding.zigzag (Dolan.Encoding.unzigzag word) = word := by
  simp only [Dolan.Encoding.unzigzag]
  split <;> simp only [Dolan.Encoding.zigzag] <;> omega

theorem journal_decode_code (changes : List (Int × Int)) : journalDecode (journalCode changes) = changes := by
  induction changes with
  | nil => rfl
  | cons entry rest ih => cases entry; simp [journalDecode, journalCode, List.map_map, Function.comp_def] at ih ⊢

theorem journal_code_decode (changes : Journal) : journalCode (journalDecode changes) = changes := by
  induction changes with
  | nil => rfl
  | cons entry rest ih => cases entry; simp [journalDecode, journalCode, List.map_map, Function.comp_def, zigzag_unzigzag] at ih ⊢

theorem journal_code_injective : Function.Injective journalCode := by
  intro first second same
  have decoded := congrArg journalDecode same
  rw [journal_decode_code, journal_decode_code] at decoded
  exact decoded

theorem journal_code_length (changes : List (Int × Int)) : (journalCode changes).length = changes.length := by
  simp [journalCode]

/-- Lookup returns the newest matching write, including repeated addresses. -/
theorem read_correct (initial : Int → Int) (changes : List (Int × Int)) (field : Int) :
    read (Dolan.Encoding.zigzag (initial field)) (journalCode changes) (Dolan.Encoding.zigzag field) =
      Dolan.Encoding.zigzag (Finite.lookup initial changes field) := by
  induction changes with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨written, datum⟩
    by_cases same : field = written
    · subst written
      simp [read, journalCode, Finite.lookup]
    · have codes : Dolan.Encoding.zigzag field ≠ Dolan.Encoding.zigzag written :=
        fun equal => same (Dolan.Encoding.zigzag_injective equal)
      have noMatch : (Dolan.Encoding.zigzag field == Dolan.Encoding.zigzag written) = false := by
        cases matched : (Dolan.Encoding.zigzag field == Dolan.Encoding.zigzag written) with
        | false => rfl
        | true => exact False.elim (codes (beq_iff_eq.mp matched))
      simpa [read, journalCode, Finite.lookup, List.lookup, same, noMatch] using ih

theorem push_correct (field datum : Int) (changes : List (Int × Int)) :
    push (Dolan.Encoding.zigzag field) (Dolan.Encoding.zigzag datum) (journalCode changes) =
      journalCode ((field, datum) :: changes) := rfl

theorem flatten_correct (changes : List (Int × Int)) :
    flatten (journalCode changes) = (Finite.encodeChanges changes).map Dolan.Encoding.zigzag := by
  induction changes with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨field, datum⟩
    change Dolan.Encoding.zigzag field :: Dolan.Encoding.zigzag datum :: flatten (journalCode rest) =
      Dolan.Encoding.zigzag field :: Dolan.Encoding.zigzag datum :: (Finite.encodeChanges rest).map Dolan.Encoding.zigzag
    rw [ih]

theorem flatten_length (changes : Journal) : (flatten changes).length = 2 * changes.length := by
  induction changes with
  | nil => rfl
  | cons entry rest ih =>
    cases entry
    simp [flatten] at ih ⊢
    omega

/-- The existing natural-list state serializer contains precisely this journal
after its four scalar entries; no extra execution or initial-memory data enters. -/
theorem serialize_journal (state : Finite.State) :
    (Finite.serializeNat state).drop 4 = flatten (journalCode state.changes) := by
  simp [Finite.serializeNat, Finite.serialize, flatten_correct]

theorem read_primrec : Primrec (fun input : (Nat × Journal) × Nat => read input.1.1 input.1.2 input.2) := by
  exact Primrec.option_getD.comp
    (Primrec.listLookup.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp Primrec.fst)

theorem push_primrec : Primrec (fun input : (Nat × Nat) × Journal => push input.1.1 input.1.2 input.2) := by
  exact Primrec.list_cons.comp Primrec.fst Primrec.snd

theorem flatten_primrec : Primrec flatten := by
  have entry : Primrec (fun pair : Nat × Nat => [pair.1, pair.2]) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  exact Primrec.list_flatMap Primrec.id (entry.comp₂ Primrec₂.right)

/-- The existing signed-word enumeration agrees with the pinned library's
concrete integer encoding; its computability certificate uses that encoding. -/
theorem zigzag_encode (word : Int) : Dolan.Encoding.zigzag word = Encodable.encode word := by
  change Dolan.Encoding.zigzag word = Equiv.intEquivNat word
  cases word <;> rfl

theorem unzigzag_ofNat (word : Nat) : Dolan.Encoding.unzigzag word = Denumerable.ofNat Int word := by
  apply Dolan.Encoding.zigzag_injective
  rw [zigzag_unzigzag, zigzag_encode]
  exact (Denumerable.encode_ofNat (α := Int) word).symm

theorem zigzag_primrec : Primrec Dolan.Encoding.zigzag :=
  Primrec.encode.of_eq fun word => (zigzag_encode word).symm

theorem unzigzag_primrec : Primrec Dolan.Encoding.unzigzag :=
  (Primrec.ofNat Int).of_eq fun word => (unzigzag_ofNat word).symm

theorem journal_code_primrec : Primrec journalCode := by
  have entry : Primrec (fun pair : Int × Int => (Dolan.Encoding.zigzag pair.1, Dolan.Encoding.zigzag pair.2)) :=
    (zigzag_primrec.comp Primrec.fst).pair (zigzag_primrec.comp Primrec.snd)
  exact Primrec.list_map Primrec.id (entry.comp₂ Primrec₂.right)

theorem journal_decode_primrec : Primrec journalDecode := by
  have entry : Primrec (fun pair : Nat × Nat => (Dolan.Encoding.unzigzag pair.1, Dolan.Encoding.unzigzag pair.2)) :=
    (unzigzag_primrec.comp Primrec.fst).pair (unzigzag_primrec.comp Primrec.snd)
  exact Primrec.list_map Primrec.id (entry.comp₂ Primrec₂.right)

end SmcTuring.SMC.Effective

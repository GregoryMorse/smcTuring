module
public import SmcTuring.SMC.FiniteExecution
public import SmcTuring.Dolan.Initialization

public section

namespace SmcTuring.SMC.Finite

@[expose] def encodeChanges : List (Int × Int) → List Int
  | [] => []
  | (field, datum) :: rest => field :: datum :: encodeChanges rest

@[expose] def decodeChanges : List Int → Option (List (Int × Int))
  | [] => some []
  | field :: datum :: rest => (decodeChanges rest).map ((field, datum) :: ·)
  | _ => none

theorem decode_changes_encode (changes : List (Int × Int)) : decodeChanges (encodeChanges changes) = some changes := by
  induction changes with
  | nil => rfl
  | cons entry rest ih => cases entry; simp [encodeChanges, decodeChanges, ih]

theorem encode_changes_length (changes : List (Int × Int)) : (encodeChanges changes).length = 2 * changes.length := by
  induction changes with
  | nil => rfl
  | cons entry rest ih =>
    cases entry
    simp only [encodeChanges, List.length_cons, ih]
    omega

/-- Four scalar words followed by alternating write addresses and values. -/
@[expose] def serialize (s : State) : List Int :=
  s.acc :: s.stack :: s.pc :: (if s.carry then 1 else 0) :: encodeChanges s.changes

@[expose] def deserialize : List Int → Option State
  | acc :: stack :: pc :: flag :: changes =>
    if flag = 0 then (decodeChanges changes).map fun journal =>
      { acc := acc, stack := stack, pc := pc, carry := false, changes := journal }
    else if flag = 1 then (decodeChanges changes).map fun journal =>
      { acc := acc, stack := stack, pc := pc, carry := true, changes := journal }
    else none
  | _ => none

theorem deserialize_serialize (s : State) : deserialize (serialize s) = some s := by
  cases s with
  | mk acc stack pc carry changes =>
    cases carry <;> simp [serialize, deserialize, decode_changes_encode]

theorem serialize_injective : Function.Injective serialize := by
  intro first second same
  have decoded := congrArg deserialize same
  rw [deserialize_serialize, deserialize_serialize] at decoded
  exact Option.some.inj decoded

theorem serialize_length (s : State) : (serialize s).length = 4 + 2 * s.changes.length := by
  simp [serialize, encode_changes_length]
  omega

/-- Signed words are encoded by the checked zigzag enumeration. A reached
state is thus a finite list of natural numbers, independent of machine width. -/
@[expose] def serializeNat (s : State) : List Nat := (serialize s).map Dolan.Encoding.zigzag

@[expose] def deserializeNat (words : List Nat) : Option State :=
  deserialize (words.map Dolan.Encoding.unzigzag)

theorem deserialize_serialize_nat (s : State) : deserializeNat (serializeNat s) = some s := by
  simp [deserializeNat, serializeNat, List.map_map, Function.comp_def, deserialize_serialize]

theorem serialize_nat_injective : Function.Injective serializeNat := by
  intro first second same
  have decoded := congrArg deserializeNat same
  rw [deserialize_serialize_nat, deserialize_serialize_nat] at decoded
  exact Option.some.inj decoded

theorem serialize_nat_length (s : State) : (serializeNat s).length = 4 + 2 * s.changes.length := by
  simpa only [serializeNat, List.length_map] using serialize_length s

end SmcTuring.SMC.Finite

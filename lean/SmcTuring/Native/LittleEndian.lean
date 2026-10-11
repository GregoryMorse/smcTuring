module
public import SmcTuring.Memory
public import Init.Data.BitVec.Lemmas

public section

namespace SmcTuring.Native.LittleEndian

abbrev Byte := BitVec 8

/-- Least-significant byte first, for precisely the supplied byte count. -/
@[expose] def encode : Nat -> Nat -> List Byte
  | 0, _ => []
  | count + 1, value => BitVec.ofNat 8 value :: encode count (value / 256)

/-- Interpret the complete byte list in radix 256. -/
@[expose] def pack : List Byte -> Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * pack rest

@[simp] theorem encode_length (count value : Nat) : (encode count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp [encode, ih]

/-- Every byte is in range, independently of its source word. -/
theorem byte_bound (byte : Byte) : byte.toNat < 256 := byte.isLt

/-- A finite byte sequence fits precisely within its unsigned word width. -/
theorem pack_bound (bytes : List Byte) : pack bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [pack]
  | cons byte rest ih =>
    have low := byte_bound byte
    simp only [pack, List.length_cons, Nat.pow_succ]
    omega

/-- No modular loss occurs when the source value fits the selected width. -/
theorem pack_encode (count value : Nat) (fits : value < 256 ^ count) :
    pack (encode count value) = value := by
  induction count generalizing value with
  | zero =>
    have zero : value = 0 := by omega
    subst value
    rfl
  | succ count ih =>
    have high : value / 256 < 256 ^ count :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr (by simpa [Nat.pow_succ] using fits)
    simp only [encode, pack, ih _ high, BitVec.toNat_ofNat]
    exact Nat.mod_add_div value 256

/-- Packing and splitting a byte list retains every original byte. -/
theorem encode_pack (bytes : List Byte) : encode bytes.length (pack bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have low := byte_bound byte
    have remainder : BitVec.ofNat 8 (byte.toNat + 256 * pack rest) = byte := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt low
    have quotient : (byte.toNat + 256 * pack rest) / 256 = pack rest := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 256), Nat.div_eq_of_lt low]
      exact Nat.zero_add _
    simp only [List.length_cons, pack, encode, remainder, quotient, ih]

/-- Radix-256 byte widths agree with the bit-vector word widths. -/
theorem radix_power (count : Nat) : (256 : Nat) ^ count = 2 ^ (8 * count) := by
  rw [Nat.pow_mul]

@[expose] def wordEncode (count : Nat) (value : BitVec (8 * count)) : List Byte :=
  encode count value.toNat

/-- Reject a truncated or overlong encoded word. -/
@[expose] def wordDecode (count : Nat) (bytes : List Byte) : Option (BitVec (8 * count)) :=
  if bytes.length = count then some (BitVec.ofNat (8 * count) (pack bytes)) else none

@[simp] theorem word_encode_length (count : Nat) (value : BitVec (8 * count)) :
    (wordEncode count value).length = count := encode_length count value.toNat

/-- Exact bit-vector round trip, including count zero and the 32/64-bit modes. -/
@[simp] theorem word_decode_encode (count : Nat) (value : BitVec (8 * count)) :
    wordDecode count (wordEncode count value) = some value := by
  have fits : value.toNat < 256 ^ count := by rw [radix_power]; exact value.isLt
  simp only [wordDecode, wordEncode, encode_length, ite_true, pack_encode count value.toNat fits]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt value.isLt]

/-- Every accepted byte sequence is the exact encoding of its decoded value. -/
theorem word_encode_decode (count : Nat) (bytes : List Byte) (value : BitVec (8 * count))
    (decoded : wordDecode count bytes = some value) : wordEncode count value = bytes := by
  unfold wordDecode at decoded
  split at decoded
  · rename_i length
    have same : BitVec.ofNat (8 * count) (pack bytes) = value := Option.some.inj decoded
    have fits : pack bytes < 2 ^ (8 * count) := by
      rw [←radix_power, ←length]
      exact pack_bound bytes
    rw [←same, wordEncode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, ←length]
    exact encode_pack bytes
  · cases decoded

theorem word_encode_injective (count : Nat) : Function.Injective (wordEncode count) := by
  intro first second same
  have decoded := congrArg (wordDecode count) same
  simpa only [word_decode_encode, Option.some.injEq] using decoded

theorem word_decode_wrong_length (count : Nat) (bytes : List Byte) (wrong : bytes.length ≠ count) :
    wordDecode count bytes = none := by simp [wordDecode, wrong]

end SmcTuring.Native.LittleEndian

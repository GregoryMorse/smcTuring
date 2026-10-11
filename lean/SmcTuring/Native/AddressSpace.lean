module
public import SmcTuring.Native.MemoryRegion

public section

namespace SmcTuring.Native.AddressSpace

open MemoryRegion

/-- The paging configuration is a parameter, not a claim of CPU support. -/
inductive Paging where
  | four | five
  deriving DecidableEq, Repr

@[expose] def Paging.linearBits : Paging → Nat
  | .four => 48
  | .five => 57

@[expose] def half (paging : Paging) : Nat := 2 ^ (paging.linearBits - 1)
@[expose] def highStart (paging : Paging) : Nat := 2 ^ 64 - half paging

/-- Ordinary unmasked linear addresses: 32-bit flat x86, or the low and high
canonical intervals for configured x64 paging. LAM is not modeled. -/
@[expose] def Valid (mode : Mode) (paging : Paging) (address : Nat) : Prop :=
  match mode with
  | .x86 => address < 2 ^ 32
  | .x64 => address < half paging ∨ (highStart paging ≤ address ∧ address < 2 ^ 64)

instance (mode : Mode) (paging : Paging) (address : Nat) : Decidable (Valid mode paging address) := by
  cases mode <;> unfold Valid <;> infer_instance

/-- Endpoints certify a whole allocation without enumerating later accesses.
An x64 interval must lie wholly in one canonical component. -/
@[expose] def Fits (mode : Mode) (paging : Paging) (region : Region) : Prop :=
  match mode with
  | .x86 => region.upper ≤ 2 ^ 32
  | .x64 => region.upper ≤ half paging ∨
      (highStart paging ≤ region.lower ∧ region.upper ≤ 2 ^ 64)

theorem region_valid (mode : Mode) (paging : Paging) (region : Region)
    (fits : Fits mode paging region) (address : Nat)
    (lower : region.lower ≤ address) (upper : address < region.upper) : Valid mode paging address := by
  cases mode with
  | x86 => change region.upper ≤ 2 ^ 32 at fits; change address < 2 ^ 32; omega
  | x64 =>
    change region.upper ≤ half paging ∨ (highStart paging ≤ region.lower ∧ region.upper ≤ 2 ^ 64) at fits
    change address < half paging ∨ (highStart paging ≤ address ∧ address < 2 ^ 64)
    rcases fits with low | high
    · exact Or.inl (Nat.lt_of_lt_of_le upper low)
    · exact Or.inr ⟨Nat.le_trans high.1 lower, Nat.lt_of_lt_of_le upper high.2⟩

/-- Every byte of a contained window is valid, including its final byte. -/
theorem contains_valid (mode : Mode) (paging : Paging) (region : Region)
    (fits : Fits mode paging region) (address count : Nat)
    (contained : region.Contains address count) (index : Fin count) : Valid mode paging (address + index.val) :=
  region_valid mode paging region fits _ (contains_byte region address count contained index).1
    (contains_byte region address count contained index).2

theorem x86_fits (paging : Paging) (region : Region) (capacity : region.upper ≤ 2 ^ 32) :
    Fits .x86 paging region := capacity

theorem x64_low_fits (paging : Paging) (region : Region) (upper : region.upper ≤ half paging) :
    Fits .x64 paging region := Or.inl upper

theorem x64_high_fits (paging : Paging) (region : Region)
    (lower : highStart paging ≤ region.lower) (upper : region.upper ≤ 2 ^ 64) :
    Fits .x64 paging region := Or.inr ⟨lower, upper⟩

/-- Finite-word representability alone does not exclude the x64 canonical hole. -/
theorem x64_gap_invalid (paging : Paging) (address : Nat)
    (lower : half paging ≤ address) (upper : address < highStart paging) :
    ¬ Valid .x64 paging address := by
  unfold Valid
  omega

end SmcTuring.Native.AddressSpace

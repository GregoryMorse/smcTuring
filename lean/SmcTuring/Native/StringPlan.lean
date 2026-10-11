module
public import SmcTuring.Native.StringCopy

public section
namespace SmcTuring.Native.StringPlan
open LittleEndian StringCopy

/-- Listing 5: largest elements first, then the remaining four/two/one bytes.
The remainder counts are zero or one, exactly the printed bit-mask tests. -/
@[expose] def widths (mode : Mode) (size : Nat) : List Nat :=
  match mode with
  | .x86 => List.replicate (size / 4) 4 ++ List.replicate ((size % 4) / 2) 2 ++ List.replicate (size % 2) 1
  | .x64 => List.replicate (size / 8) 8 ++ List.replicate ((size % 8) / 4) 4 ++ List.replicate ((size % 4) / 2) 2 ++ List.replicate (size % 2) 1

@[expose] def Legal (mode : Mode) (width : Nat) : Prop := width = 1 ∨ width = 2 ∨ width = 4 ∨ (mode = .x64 ∧ width = 8)

@[expose] def opcode (width : Nat) : List Byte :=
  if width = 1 then [0xA4] else if width = 2 then [0x66,0xA5] else if width = 4 then [0xA5] else if width = 8 then [0x48,0xA5] else []
@[expose] def bytes (mode : Mode) (size : Nat) : List Byte := ((widths mode size).map opcode).flatten

theorem sum_replicate (length width : Nat) : (List.replicate length width).sum = length * width := by
  induction length with
  | zero => simp
  | succ length ih => simp only [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega

theorem total (mode : Mode) (size : Nat) : count (widths mode size) = size := by
  cases mode <;> simp only [count, widths, List.sum_append, sum_replicate] <;> omega

theorem remainder_two (size : Nat) : (size % 4) / 2 ≤ 1 := by omega

theorem remainder_four (size : Nat) : (size % 8) / 4 ≤ 1 := by omega

theorem remainder_one (size : Nat) : size % 2 ≤ 1 := by omega

theorem two_bit_count (size : Nat) : (if ((size % 4) &&& 2) = 0 then 0 else 1) = (size % 4) / 2 := by
  have cases : size % 4 = 0 ∨ size % 4 = 1 ∨ size % 4 = 2 ∨ size % 4 = 3 := by omega
  rcases cases with h | h | h | h <;> rw [h] <;> decide

theorem four_bit_count (size : Nat) : (if ((size % 8) &&& 4) = 0 then 0 else 1) = (size % 8) / 4 := by
  have cases : size % 8 = 0 ∨ size % 8 = 1 ∨ size % 8 = 2 ∨ size % 8 = 3 ∨ size % 8 = 4 ∨ size % 8 = 5 ∨ size % 8 = 6 ∨ size % 8 = 7 := by omega
  rcases cases with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem one_bit_count (size : Nat) : (if (size &&& 1) = 0 then 0 else 1) = size % 2 := by
  rw [Nat.and_one_is_mod]
  have cases : size % 2 = 0 ∨ size % 2 = 1 := by omega
  rcases cases with h | h <;> rw [h] <;> decide

@[expose] def literalWidths (mode : Mode) (size : Nat) : List Nat :=
  let two := List.replicate (if ((size % 4) &&& 2) = 0 then 0 else 1) 2
  let one := List.replicate (if (size &&& 1) = 0 then 0 else 1) 1
  match mode with
  | .x86 => List.replicate (size / 4) 4 ++ two ++ one
  | .x64 => List.replicate (size / 8) 8 ++ List.replicate (if ((size % 8) &&& 4) = 0 then 0 else 1) 4 ++ two ++ one

theorem literal_widths (mode : Mode) (size : Nat) : literalWidths mode size = widths mode size := by
  unfold literalWidths
  rw [two_bit_count, one_bit_count]
  cases mode with
  | x86 => rfl
  | x64 => rw [four_bit_count]; rfl

theorem legal (mode : Mode) (size : Nat) (width : Nat) (member : width ∈ widths mode size) : Legal mode width := by
  unfold Legal
  cases mode with
  | x86 =>
    simp only [widths,List.mem_append,List.mem_replicate] at member
    rcases member with (⟨_,four⟩ | ⟨_,two⟩) | ⟨_,one⟩
    · exact Or.inr (Or.inr (Or.inl four))
    · exact Or.inr (Or.inl two)
    · exact Or.inl one
  | x64 =>
    simp only [widths,List.mem_append,List.mem_replicate] at member
    rcases member with ((⟨_,eight⟩ | ⟨_,four⟩) | ⟨_,two⟩) | ⟨_,one⟩
    · exact Or.inr (Or.inr (Or.inr ⟨rfl,eight⟩))
    · exact Or.inr (Or.inr (Or.inl four))
    · exact Or.inr (Or.inl two)
    · exact Or.inl one

theorem positive (mode : Mode) (size : Nat) (width : Nat) (member : width ∈ widths mode size) : 0 < width := by
  rcases legal mode size width member with one | two | four | eight
  · omega
  · omega
  · omega
  · omega

theorem opcode_nonempty (mode : Mode) (width : Nat) (legal : Legal mode width) : opcode width ≠ [] := by
  rcases legal with one | two | four | eight
  · subst width; decide
  · subst width; decide
  · subst width; decide
  · rcases eight with ⟨_, value⟩; subst width; decide

theorem opcode_length (mode : Mode) (width : Nat) (legal : Legal mode width) :
    (opcode width).length = 1 ∨ (opcode width).length = 2 := by
  rcases legal with one | two | four | eight
  · subst width; exact Or.inl rfl
  · subst width; exact Or.inr rfl
  · subst width; exact Or.inl rfl
  · rcases eight with ⟨_, value⟩; subst width; exact Or.inr rfl

/-- Arbitrary input bytes, exact printed element plan and both placement orders. -/
theorem correct (mode : Mode) (size : Nat) (state : State) (separate : Apart state.source state.destination size) :
    run (widths mode size) state = ⟨state.source + size, state.destination + size,
      ByteMemory.putBytes state.memory state.destination (ByteMemory.bytesAt state.memory state.source size)⟩ := by
  have effect := StringCopy.effect (widths mode size) state (by rwa [total])
  simpa only [total] using effect

theorem copied (mode : Mode) (size : Nat) (state : State) (separate : Apart state.source state.destination size) :
    ByteMemory.bytesAt (run (widths mode size) state).memory state.destination size = ByteMemory.bytesAt state.memory state.source size := by
  have result := StringCopy.copied (widths mode size) state (by rwa [total])
  simpa only [total] using result

theorem source_preserved (mode : Mode) (size : Nat) (state : State) (separate : Apart state.source state.destination size) :
    ByteMemory.bytesAt (run (widths mode size) state).memory state.source size = ByteMemory.bytesAt state.memory state.source size := by
  have result := StringCopy.source_preserved (widths mode size) state (by rwa [total])
  simpa only [total] using result

theorem frame (mode : Mode) (size : Nat) (state : State) (separate : Apart state.source state.destination size) (position : Nat)
    (outside : ¬ByteMemory.Inside state.destination size position) :
    (run (widths mode size) state).memory position = state.memory position := by
  have result := StringCopy.frame (widths mode size) state (by rwa [total]) position (by rwa [total])
  exact result

end SmcTuring.Native.StringPlan

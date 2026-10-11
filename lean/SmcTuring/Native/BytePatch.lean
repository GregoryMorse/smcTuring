module
public import SmcTuring.Native.Writes

public section
namespace SmcTuring.Native.BytePatch
open ByteMemory LittleEndian

theorem put_append (memory : Memory) (address : Nat) (leading trailing : List Byte) :
    putBytes memory address (leading++trailing) =
      putBytes (putBytes memory address leading) (address+leading.length) trailing := by
  funext position
  by_cases inTail : Inside (address+leading.length) trailing.length position
  · have whole : Inside address (leading++trailing).length position := by
      simp only [Inside,List.length_append]
      rcases inTail with ⟨lo,hi⟩
      omega
    have index : leading.length ≤ position-address := by
      rcases inTail with ⟨lo,hi⟩
      omega
    simp only [putBytes,dite_eq_left whole,dite_eq_left inTail,List.getElem_append_right index,Nat.sub_sub]
  · by_cases inHead : Inside address leading.length position
    · have whole : Inside address (leading++trailing).length position := by
        simp only [Inside,List.length_append]
        rcases inHead with ⟨lo,hi⟩
        omega
      have index : position-address < leading.length := by
        rcases inHead with ⟨lo,hi⟩
        omega
      simp only [putBytes,dite_eq_left whole,dite_eq_right inTail,dite_eq_left inHead,List.getElem_append_left index]
    · have outside : ¬Inside address (leading++trailing).length position := by
        simp only [Inside,List.length_append] at *
        omega
      simp only [putBytes,dite_eq_right outside,dite_eq_right inTail,dite_eq_right inHead]

theorem middle (memory : Memory) (address : Nat) (leading old fresh trailing : List Byte)
    (same : old.length = fresh.length) :
    putBytes (putBytes memory address (leading++old++trailing)) (address+leading.length) fresh =
      putBytes memory address (leading++fresh++trailing) := by
  calc
    _ = putBytes (putBytes (putBytes memory address (leading++old))
        (address+leading.length+old.length) trailing) (address+leading.length) fresh := by
      rw [put_append memory address (leading++old) trailing]
      simp only [List.length_append,Nat.add_assoc]
    _ = putBytes (putBytes (putBytes memory address (leading++old))
        (address+leading.length) fresh) (address+leading.length+old.length) trailing := by
      apply Writes.put_bytes_commute
      intro position inside
      simp only [Inside] at *
      omega
    _ = putBytes (putBytes memory address (leading++fresh))
        (address+leading.length+old.length) trailing := by
      rw [ByteMemory.patch_payload memory address leading old fresh same]
    _ = _ := by
      rw [put_append memory address (leading++fresh) trailing]
      simp only [List.length_append,same,Nat.add_assoc]

theorem current (memory : Memory) (address : Nat) (leading old fresh trailing : List Byte)
    (same : old.length = fresh.length)
    (intact : bytesAt memory address (leading++old++trailing).length = leading++old++trailing) :
    bytesAt (putBytes memory (address+leading.length) fresh) address
      (leading++fresh++trailing).length = leading++fresh++trailing := by
  have back := ByteMemory.put_current memory address (leading++old++trailing) intact
  rw [←back,middle memory address leading old fresh trailing same]
  exact ByteMemory.bytes_at_put _ _ _

end SmcTuring.Native.BytePatch

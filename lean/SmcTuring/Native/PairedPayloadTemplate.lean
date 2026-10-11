module
public import SmcTuring.Native.PayloadTemplate
public import SmcTuring.Native.StringWindow

public section
namespace SmcTuring.Native.PairedPayloadTemplate
open LittleEndian

@[expose] def firstField (start : Nat) (front : List Byte) : Nat := start+front.length
@[expose] def secondField (mode : Mode) (start : Nat) (front middle : List Byte) : Nat :=
  firstField start front+mode.wordBytes+middle.length
@[expose] def span (mode : Mode) (front middle last : List Byte) : Nat :=
  front.length+mode.wordBytes+middle.length+mode.wordBytes+last.length

/-- Both operand words may contain arbitrary current bytes. Every byte in
the three intervening fixed segments remains part of the original encoding. -/
@[expose] def Intact (mode : Mode) (memory : ByteMemory.Memory) (start : Nat)
    (front middle last : List Byte) : Prop :=
  PayloadTemplate.Prefix memory start front ∧
  PayloadTemplate.Prefix memory (firstField start front+mode.wordBytes) middle ∧
  PayloadTemplate.Prefix memory (secondField mode start front middle+mode.wordBytes) last

theorem current (mode : Mode) (memory : ByteMemory.Memory) (start : Nat)
    (front middle last : List Byte) (intact : Intact mode memory start front middle last) :
    ByteMemory.bytesAt memory start (span mode front middle last) =
      front ++ wordEncode mode.wordBytes (Protected.wordAt mode memory (firstField start front)) ++
      middle ++ wordEncode mode.wordBytes (Protected.wordAt mode memory (secondField mode start front middle)) ++ last := by
  rcases intact with ⟨a,b,c⟩
  simp only [PayloadTemplate.Prefix,secondField,firstField,Nat.add_assoc] at a b c ⊢
  simp only [span,Nat.add_assoc,Protected.bytes_at_append,←Protected.word_at_encoded]
  rw [a,b,c]
  simp only [List.append_assoc]

theorem initial (mode : Mode) (memory : ByteMemory.Memory) (start : Nat)
    (front middle last : List Byte) (left right : Word mode)
    (present : ByteMemory.bytesAt memory start
      (front++wordEncode mode.wordBytes left++middle++wordEncode mode.wordBytes right++last).length =
      front++wordEncode mode.wordBytes left++middle++wordEncode mode.wordBytes right++last) :
    Intact mode memory start front middle last := by
  refine ⟨?_,?_,?_⟩
  · exact StringWindow.packet_window memory start [] front
      (wordEncode mode.wordBytes left++middle++wordEncode mode.wordBytes right++last)
      (by simpa only [List.nil_append,List.append_assoc] using present)
  · have h := StringWindow.packet_window memory start (front++wordEncode mode.wordBytes left)
      middle (wordEncode mode.wordBytes right++last) (by simpa only [List.append_assoc] using present)
    simpa only [PayloadTemplate.Prefix,firstField,List.length_append,word_encode_length,Nat.add_assoc] using h
  · have h := StringWindow.packet_window memory start
      (front++wordEncode mode.wordBytes left++middle++wordEncode mode.wordBytes right) last []
      (by simpa only [List.append_nil] using present)
    simpa only [PayloadTemplate.Prefix,firstField,secondField,List.length_append,word_encode_length,Nat.add_assoc] using h

theorem frame (mode : Mode) (memory : ByteMemory.Memory) (start : Nat)
    (front middle last : List Byte) (address : Nat) (bytes : List Byte)
    (intact : Intact mode memory start front middle last)
    (outside : address+bytes.length≤start ∨ start+span mode front middle last≤address) :
    Intact mode (ByteMemory.putBytes memory address bytes) start front middle last := by
  rcases intact with ⟨a,b,c⟩
  refine ⟨PayloadTemplate.frame _ _ _ _ _ a ?_,PayloadTemplate.frame _ _ _ _ _ b ?_,
    PayloadTemplate.frame _ _ _ _ _ c ?_⟩ <;>
    intro index inside <;> have bound := index.isLt <;>
    unfold ByteMemory.Inside at inside <;>
    simp only [secondField,firstField,span] at * <;> rcases outside with before | after <;> omega

/-- The entire architectural packet fits in either cursor operand. The
other operand and all fixed segments are protected even for partial writes. -/
theorem operand_store (mode : Mode) (memory : ByteMemory.Memory) (start : Nat)
    (front middle last : List Byte) (address : Nat) (bytes : List Byte)
    (intact : Intact mode memory start front middle last)
    (owned : (firstField start front≤address ∧ address+bytes.length≤firstField start front+mode.wordBytes) ∨
      (secondField mode start front middle≤address ∧ address+bytes.length≤secondField mode start front middle+mode.wordBytes)) :
    Intact mode (ByteMemory.putBytes memory address bytes) start front middle last := by
  rcases intact with ⟨a,b,c⟩
  refine ⟨PayloadTemplate.frame _ _ _ _ _ a ?_,PayloadTemplate.frame _ _ _ _ _ b ?_,
    PayloadTemplate.frame _ _ _ _ _ c ?_⟩ <;>
    intro index inside <;> have bound := index.isLt <;>
    unfold ByteMemory.Inside at inside <;>
    simp only [secondField,firstField] at * <;> rcases owned with left | right <;> omega

theorem store (mode : Mode) (memory : ByteMemory.Memory) (start : Nat)
    (front middle last : List Byte) (address : Nat) (bytes : List Byte)
    (intact : Intact mode memory start front middle last)
    (allowed : ((firstField start front≤address ∧ address+bytes.length≤firstField start front+mode.wordBytes) ∨
      (secondField mode start front middle≤address ∧ address+bytes.length≤secondField mode start front middle+mode.wordBytes)) ∨
      (address+bytes.length≤start ∨ start+span mode front middle last≤address)) :
    Intact mode (ByteMemory.putBytes memory address bytes) start front middle last ∧
    ByteMemory.bytesAt (ByteMemory.putBytes memory address bytes) start (span mode front middle last) =
      front ++ wordEncode mode.wordBytes (Protected.wordAt mode (ByteMemory.putBytes memory address bytes) (firstField start front)) ++
      middle ++ wordEncode mode.wordBytes (Protected.wordAt mode (ByteMemory.putBytes memory address bytes) (secondField mode start front middle)) ++ last := by
  have kept : Intact mode (ByteMemory.putBytes memory address bytes) start front middle last := by
    rcases allowed with operand | outside
    · exact operand_store mode memory start front middle last address bytes intact operand
    · exact frame mode memory start front middle last address bytes intact outside
  exact ⟨kept,current mode _ start front middle last kept⟩

end SmcTuring.Native.PairedPayloadTemplate

module
public import SmcTuring.Native.StringInitTemplates

public section
namespace SmcTuring.Native.RelativeCallTemplate

@[expose] def Intact (pc : Nat) (memory : ByteMemory.Memory) : Prop := PayloadTemplate.Prefix memory pc [0xe8]
@[expose] def Decodes (mode : Mode) (pc : Nat) (memory : ByteMemory.Memory) : Prop :=
  StringStack.fetch mode memory pc=some (StringWrites.liftNative mode (.callRelative (Protected.wordAt .x86 memory (pc+1))))

theorem initial (mode : Mode) (pc : Nat) (displacement : BitVec 32) (memory : ByteMemory.Memory)
    (packet : ByteMemory.bytesAt memory pc 5=Native.encode mode (.callRelative displacement)) : Intact pc memory := by
  have image : ByteMemory.bytesAt memory pc ([0xe8]++LittleEndian.wordEncode 4 displacement).length=
      [0xe8]++LittleEndian.wordEncode 4 displacement := packet
  exact StringWindow.packet_window memory pc [] [0xe8] (LittleEndian.wordEncode 4 displacement)
    (by simpa only [List.nil_append] using image)

theorem current (mode : Mode) (pc : Nat) (memory : ByteMemory.Memory) (intact : Intact pc memory) :
    ByteMemory.bytesAt memory pc 5=Native.encode mode (.callRelative (Protected.wordAt .x86 memory (pc+1))) := by
  exact PayloadTemplate.current .x86 memory pc [0xe8] intact

theorem decodes (mode : Mode) (pc : Nat) (memory : ByteMemory.Memory) (intact : Intact pc memory) : Decodes mode pc memory :=
  StringEncodedTemplates.string_fetch mode memory pc _
    (StringForm.fetch_current_encoding mode memory pc (.native (.callRelative (Protected.wordAt .x86 memory (pc+1))))
      (by trivial) (current mode pc memory intact))

theorem frame (pc : Nat) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : Intact pc memory) (outside : address+packet.length≤pc ∨ pc+1≤address) :
    Intact pc (ByteMemory.putBytes memory address packet) := by
  apply PayloadTemplate.frame memory pc [0xe8] address packet intact
  intro index inside
  have bound : index.val<1 := index.isLt
  unfold ByteMemory.Inside at inside
  rcases outside with before | after <;> omega

end SmcTuring.Native.RelativeCallTemplate

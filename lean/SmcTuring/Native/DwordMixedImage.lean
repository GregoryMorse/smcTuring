module
public import SmcTuring.Native.DwordImage
public import SmcTuring.Native.MixedDword
public import SmcTuring.Native.ByteWindow

public section
namespace SmcTuring.Native.DwordMixedImage

theorem fetched (mode : Mode) (state : Execution.State mode) (pc : Nat)
    (form : DwordCode.Form mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (fits : pc < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory pc (DwordCode.encode mode form).length =
      DwordCode.encode mode form) :
    MixedDword.fetch mode state.memory state.pc.toNat = some (.copy form) := by
  rw [location,Arithmetic.encode_nat_toNat mode pc fits]
  exact MixedDword.copy_encoding mode state.memory pc form current

/-- Initial helper packets and static placement derive all three actual
mixed-decoder fetches, including the restored source before the last fetch. -/
theorem trace (mode : Mode) (lay : DwordLayout.Layout)
    (valid : DwordLayout.Admissible mode lay) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode lay.start)
    (intact : DwordImage.Intact mode lay state.memory) :
    MixedDword.Trace mode state ((DwordLayout.program mode lay).map MixedDword.Form.copy)
      (DwordEffects.finish mode lay state) := by
  have firstPacket := intact ⟨lay.start,.fixed (DwordImage.firstCode mode lay)⟩ (List.Mem.head _)
  change ByteMemory.bytesAt state.memory lay.start
    (Native.encode .x86 (DwordImage.firstCode mode lay)).length =
    Native.encode .x86 (DwordImage.firstCode mode lay) at firstPacket
  rw [←(DwordImage.byte_bindings mode lay).1] at firstPacket
  have firstFits : lay.start < 2 ^ (8 * mode.wordBytes) := by
    have high : DwordLayout.endPC mode lay < 2 ^ (8 * mode.wordBytes) := valid.codeFits
    unfold DwordLayout.endPC DwordLayout.thirdPC DwordLayout.secondPC at high
    omega
  have firstFetch := fetched mode state lay.start (DwordLayout.first mode lay)
    entry firstFits firstPacket
  have swappedIntact := DwordImage.swapped_intact mode lay valid state
    entry intact
  have secondPacket := swappedIntact
    ⟨DwordLayout.secondPC mode lay,.fixed (DwordImage.secondCode mode lay)⟩
    (List.Mem.tail _ (List.Mem.head _))
  change ByteMemory.bytesAt (DwordEffects.swapped mode lay state).memory (DwordLayout.secondPC mode lay)
    (Native.encode .x86 (DwordImage.secondCode mode lay)).length =
    Native.encode .x86 (DwordImage.secondCode mode lay) at secondPacket
  rw [←(DwordImage.byte_bindings mode lay).2.1] at secondPacket
  have secondFits : DwordLayout.secondPC mode lay < 2 ^ (8 * mode.wordBytes) := by
    have high : DwordLayout.endPC mode lay < 2 ^ (8 * mode.wordBytes) := valid.codeFits
    unfold DwordLayout.endPC DwordLayout.thirdPC at high
    omega
  have secondFetch := fetched mode (DwordEffects.swapped mode lay state)
    (DwordLayout.secondPC mode lay) (DwordLayout.second mode lay)
    (DwordEffects.swapped_pc mode lay valid state entry)
    secondFits secondPacket
  have storedIntact := DwordImage.stored_intact mode lay valid state
    entry intact
  have thirdPacket := storedIntact
    ⟨DwordLayout.thirdPC mode lay,.fixed (DwordImage.thirdCode mode lay)⟩
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  change ByteMemory.bytesAt (DwordEffects.stored mode lay state).memory (DwordLayout.thirdPC mode lay)
    (Native.encode .x86 (DwordImage.thirdCode mode lay)).length =
    Native.encode .x86 (DwordImage.thirdCode mode lay) at thirdPacket
  rw [←(DwordImage.byte_bindings mode lay).2.2] at thirdPacket
  have thirdFits : DwordLayout.thirdPC mode lay < 2 ^ (8 * mode.wordBytes) := by
    have high : DwordLayout.endPC mode lay < 2 ^ (8 * mode.wordBytes) := valid.codeFits
    unfold DwordLayout.endPC at high
    omega
  have thirdFetch := fetched mode (DwordEffects.stored mode lay state)
    (DwordLayout.thirdPC mode lay) (DwordLayout.third mode lay)
    (DwordEffects.stored_pc mode lay valid state entry)
    thirdFits thirdPacket
  change MixedDword.Trace mode state
    [.copy (DwordLayout.first mode lay),.copy (DwordLayout.second mode lay),
      .copy (DwordLayout.third mode lay)] (DwordEffects.finish mode lay state)
  apply MixedDword.Trace.step firstFetch
  change MixedDword.Trace mode (DwordEffects.swapped mode lay state)
    [.copy (DwordLayout.second mode lay),.copy (DwordLayout.third mode lay)] _
  apply MixedDword.Trace.step secondFetch
  change MixedDword.Trace mode (DwordEffects.stored mode lay state)
    [.copy (DwordLayout.third mode lay)] _
  apply MixedDword.Trace.step thirdFetch
  exact MixedDword.Trace.nil _

@[expose] def bytes (mode : Mode) (layout : DwordLayout.Layout) : List LittleEndian.Byte :=
  DwordCode.encode mode (DwordLayout.first mode layout) ++
    DwordCode.encode mode (DwordLayout.second mode layout) ++
    DwordCode.encode mode (DwordLayout.third mode layout)

theorem bytes_length (mode : Mode) (layout : DwordLayout.Layout) :
    (bytes mode layout).length = DwordLayout.span mode := by
  simp only [bytes,List.length_append,DwordCode.encode_length,
    (DwordLayout.lengths mode layout).1,(DwordLayout.lengths mode layout).2.1,
    (DwordLayout.lengths mode layout).2.2]
  cases mode <;> rfl

/-- One concatenated helper image supplies the three initial packet images. -/
theorem intact_of_bytes (mode : Mode) (layout : DwordLayout.Layout)
    (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory layout.start (bytes mode layout).length = bytes mode layout) :
    DwordImage.Intact mode layout memory := by
  have a := ByteWindow.packet memory layout.start []
    (DwordCode.encode mode (DwordLayout.first mode layout))
    (DwordCode.encode mode (DwordLayout.second mode layout) ++
      DwordCode.encode mode (DwordLayout.third mode layout))
    (by simpa [bytes,List.append_assoc] using current)
  have b := ByteWindow.packet memory layout.start
    (DwordCode.encode mode (DwordLayout.first mode layout))
    (DwordCode.encode mode (DwordLayout.second mode layout))
    (DwordCode.encode mode (DwordLayout.third mode layout))
    (by simpa [bytes,List.append_assoc] using current)
  have c := ByteWindow.packet memory layout.start
    (DwordCode.encode mode (DwordLayout.first mode layout) ++
      DwordCode.encode mode (DwordLayout.second mode layout))
    (DwordCode.encode mode (DwordLayout.third mode layout)) []
    (by simpa [bytes,List.append_assoc] using current)
  simp only [DwordCode.encode_length,(DwordLayout.lengths mode layout).1,
    show layout.start+6 = DwordLayout.secondPC mode layout from rfl] at b
  simp only [List.length_append,DwordCode.encode_length,
    (DwordLayout.lengths mode layout).1,(DwordLayout.lengths mode layout).2.1] at c
  have third : layout.start + (6 + DwordLayout.storeSize mode) = DwordLayout.thirdPC mode layout := by
    simp only [DwordLayout.thirdPC,DwordLayout.secondPC,Nat.add_assoc]
  rw [third] at c
  intro entry member
  change List.Mem entry
    [⟨layout.start,.fixed (DwordImage.firstCode mode layout)⟩,
     ⟨DwordLayout.secondPC mode layout,
       .fixed (DwordImage.secondCode mode layout)⟩,
     ⟨DwordLayout.thirdPC mode layout,
       .fixed (DwordImage.thirdCode mode layout)⟩] at member
  cases member with
  | head =>
      change ByteMemory.bytesAt memory layout.start
        (Native.encode .x86 (DwordImage.firstCode mode layout)).length =
        Native.encode .x86 (DwordImage.firstCode mode layout)
      rw [←(DwordImage.byte_bindings mode layout).1]
      exact a
  | tail _ rest =>
      cases rest with
      | head =>
          change ByteMemory.bytesAt memory (DwordLayout.secondPC mode layout)
            (Native.encode .x86 (DwordImage.secondCode mode layout)).length =
            Native.encode .x86 (DwordImage.secondCode mode layout)
          rw [←(DwordImage.byte_bindings mode layout).2.1]
          simpa only [DwordCode.encode_length] using b
      | tail _ last =>
          cases last with
          | head =>
              change ByteMemory.bytesAt memory (DwordLayout.thirdPC mode layout)
                (Native.encode .x86 (DwordImage.thirdCode mode layout)).length =
                Native.encode .x86 (DwordImage.thirdCode mode layout)
              rw [←(DwordImage.byte_bindings mode layout).2.2]
              exact c
          | tail _ empty => cases empty

/-- A disjoint DWORD write preserves a complete byte window. -/
theorem bytes_frame (memory : ByteMemory.Memory) (field start count : Nat) (value : BitVec 32)
    (outside : field+4 ≤ start ∨ start+count ≤ field) :
    ByteMemory.bytesAt (DwordCode.put memory field value) start count =
      ByteMemory.bytesAt memory start count := by
  apply ByteMemory.bytes_at_frame
  intro index
  have bound := index.isLt
  simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
  rcases outside with before | after <;> omega

end SmcTuring.Native.DwordMixedImage

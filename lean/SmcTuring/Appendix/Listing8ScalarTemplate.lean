module
public import SmcTuring.Native.PayloadTemplate
public import SmcTuring.Native.StringStoreWrites
public import SmcTuring.Native.StringDwordWritesBridge
public import SmcTuring.Native.DwordOwner

public section
namespace SmcTuring.Appendix.Listing8ScalarTemplate
open Native

@[expose] def fixed (displacement : BitVec 32) :=
  [0xc7,0x05] ++ LittleEndian.wordEncode 4 displacement
@[expose] def Intact (pc : Nat) (displacement : BitVec 32) (memory : ByteMemory.Memory) :=
  PayloadTemplate.Prefix memory pc (fixed displacement)

theorem fixed_length (displacement : BitVec 32) : (fixed displacement).length=6 := by
  simp only [fixed,List.length_append,List.length_cons,List.length_nil,LittleEndian.word_encode_length]

theorem initial (pc : Nat) (displacement value : BitVec 32) (memory : ByteMemory.Memory)
    (packet : ByteMemory.bytesAt memory pc 10=DwordArithmetic.encode (.store displacement value)) :
    Intact pc displacement memory := by
  have head := ByteWindow.packet memory pc [] (fixed displacement) (LittleEndian.wordEncode 4 value)
    (by simpa only [List.nil_append,List.length_append,fixed_length,LittleEndian.word_encode_length,
      DwordArithmetic.encode,fixed,List.length_cons,List.length_nil] using packet)
  simpa only [Intact,PayloadTemplate.Prefix,List.length_nil,Nat.add_zero] using head

theorem current (pc : Nat) (displacement : BitVec 32) (memory : ByteMemory.Memory)
    (intact : Intact pc displacement memory) :
    ByteMemory.bytesAt memory pc 10=
      DwordArithmetic.encode (.store displacement (Protected.wordAt .x86 memory (pc+6))) := by
  have ready := PayloadTemplate.current .x86 memory pc (fixed displacement) intact
  rw [fixed_length] at ready
  simpa only [Mode.wordBytes,DwordArithmetic.encode,fixed] using ready

/-- Every intermediate partial store wholly within the four-byte immediate
retains a valid current scalar instruction. -/
theorem operand_store (pc : Nat) (displacement : BitVec 32) (memory : ByteMemory.Memory)
    (intact : Intact pc displacement memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (lower : pc+6≤address) (upper : address+bytes.length≤pc+10) :
    Intact pc displacement (ByteMemory.putBytes memory address bytes) := by
  exact (PayloadTemplate.operand_store .x86 memory pc (fixed displacement) address bytes intact
    (by simpa only [fixed_length] using lower)
    (by simpa only [fixed_length,Mode.wordBytes] using upper)).1

theorem frame (pc : Nat) (displacement : BitVec 32) (memory : ByteMemory.Memory)
    (intact : Intact pc displacement memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (apart : address+bytes.length≤pc ∨ pc+10≤address) :
    Intact pc displacement (ByteMemory.putBytes memory address bytes) := by
  apply PayloadTemplate.frame memory pc (fixed displacement) address bytes intact
  intro index inside
  have small : index.val<6 := by simpa only [fixed_length] using index.isLt
  unfold ByteMemory.Inside at inside
  rcases apart with before | after <;> omega

theorem decodes (mode : Mode) (pc : Nat) (displacement : BitVec 32) (memory : ByteMemory.Memory)
    (intact : Intact pc displacement memory) :
    StringStack.fetch mode memory pc=some (StringStoreWrites.liftDword mode
      (StringDword.store mode displacement (Protected.wordAt .x86 memory (pc+6)))) :=
  StringStack.previous_fetch mode memory pc _ (StringControl.previous_fetch mode memory pc _
    (StringDword.store_encoding mode memory pc _ _ (current pc displacement memory intact)))

theorem original (mode : Mode) (pc : Nat) (value : BitVec 32) (memory : ByteMemory.Memory)
    (packet : ByteMemory.bytesAt memory pc 10=DwordOwner.bytes mode pc value) :
    Intact pc (Relocation.memoryDisp mode (pc+10) (pc+6)) memory := by
  exact initial pc _ value memory packet

/-- The actual architectural store of a located printed scalar targets the
whole declared immediate. Its resulting current value and decoding are proved. -/
theorem located_store (mode : Mode) (pc owner : Nat) (value : BitVec 32) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (reach : mode=.x64 → Relocation.SignedDelta (pc+10) (owner+6))
    (fits : owner+10<2^(8*mode.wordBytes)) (displacement : BitVec 32)
    (intact : Intact owner displacement state.principal.memory) :
    let form := StringStoreWrites.liftDword mode (StringDword.store mode
      (Relocation.memoryDisp mode (pc+10) (owner+6)) value)
    (StringWrites.packet mode form state).address=owner+6 ∧
    (StringWrites.packet mode form state).bytes=LittleEndian.wordEncode 4 value ∧
    Intact owner displacement (StringStack.execute mode form state).principal.memory ∧
    StringStack.fetch mode (StringStack.execute mode form state).principal.memory owner=
      some (StringStoreWrites.liftDword mode (StringDword.store mode displacement value)) := by
  let form := StringStoreWrites.liftDword mode (StringDword.store mode
    (Relocation.memoryDisp mode (pc+10) (owner+6)) value)
  have hits := DwordArithmetic.located_address mode (.store 0 value) pc (owner+6) state.principal rfl entry reach
  change DwordArithmetic.address mode (.store (Relocation.memoryDisp mode (pc+10) (owner+6)) value)
    state.principal=Arithmetic.encodeNat mode (owner+6) at hits
  have addr : (StringWrites.packet mode form state).address=owner+6 := by
    rw [StringStoreWrites.address,hits,Arithmetic.encode_nat_toNat mode _ (by omega)]
  have data : (StringWrites.packet mode form state).bytes=LittleEndian.wordEncode 4 value := by cases mode <;> rfl
  have memory : (StringStack.execute mode form state).principal.memory=
      ByteMemory.putWord .x86 state.principal.memory (owner+6) value := by
    rw [StringWrites.execute_memory,addr,data];rfl
  have kept : Intact owner displacement (StringStack.execute mode form state).principal.memory := by
    rw [memory]
    exact operand_store owner displacement state.principal.memory intact (owner+6) (LittleEndian.wordEncode 4 value) (by omega)
      (by simp only [LittleEndian.word_encode_length];omega)
  refine ⟨addr,data,kept,?_⟩
  have live : Protected.wordAt .x86 (StringStack.execute mode form state).principal.memory (owner+6)=value := by
    rw [memory]
    exact Protected.word_at_put .x86 state.principal.memory (owner+6) value
  simpa only [live] using decodes mode owner displacement (StringStack.execute mode form state).principal.memory kept

end SmcTuring.Appendix.Listing8ScalarTemplate

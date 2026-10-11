module
public import SmcTuring.Appendix.Listing8NodeTable

public section
namespace SmcTuring.Appendix.Listing8LiveNodePacket
open Native Listing8Prototypes
@[expose] def headerBytes (mode : Mode) (entry : Nat) :=
  ([0xc7,0x05] : List LittleEndian.Byte)++LittleEndian.wordEncode 4 (Relocation.memoryDisp mode (entry+10) (entry+6))
theorem prefix_length (mode : Mode) (entry : Nat) : (headerBytes mode entry).length=6 := by
  simp only [headerBytes,List.length_append,List.length_cons,List.length_nil,LittleEndian.word_encode_length]
theorem shape (mode : Mode) (entry : Nat) (symbol : BitVec 32) (back forward : Word mode) :
    nodeBytes mode entry symbol back forward=
      (headerBytes mode entry++LittleEndian.wordEncode 4 symbol)++
      (pointerBytes mode (backEntry mode entry) back++pointerBytes mode (forwardEntry mode entry) forward) := by
  simp only [nodeBytes,DwordOwner.bytes,DwordOwner.form,DwordStore.emit,DwordStore.encode,DwordStore.common,ByteCode.encode,ByteCode.ImmediateOp.tag,headerBytes,List.append_assoc]

/-- The live DWORD bytes are recovered from their total byte decoder. -/
theorem symbol_bytes (memory : ByteMemory.Memory) (entry : Nat) (symbol : BitVec 32)
    (value : DwordCode.get memory (entry+6)=symbol) :
    ByteMemory.bytesAt memory (entry+6) 4=LittleEndian.wordEncode 4 symbol := by
  exact (LittleEndian.word_encode_decode 4 _ symbol (by change ByteMemory.readWord .x86 memory (entry+6)=some symbol;rw [DwordCode.read_total,value])).symm

theorem windows (mode : Mode) (entry : Nat) (symbol : BitVec 32) (back forward : Word mode)
    (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory entry (nodeSpan mode)=nodeBytes mode entry symbol back forward) :
    ByteMemory.bytesAt memory entry 6=headerBytes mode entry ∧
    ByteMemory.bytesAt memory (entry+10) (2*pointerSpan mode)=
      pointerBytes mode (backEntry mode entry) back++pointerBytes mode (forwardEntry mode entry) forward := by
  have packet : ByteMemory.bytesAt memory entry
      ((headerBytes mode entry++LittleEndian.wordEncode 4 symbol)++
        (pointerBytes mode (backEntry mode entry) back++pointerBytes mode (forwardEntry mode entry) forward)).length=
      (headerBytes mode entry++LittleEndian.wordEncode 4 symbol)++
        (pointerBytes mode (backEntry mode entry) back++pointerBytes mode (forwardEntry mode entry) forward) := by
    rw [←shape,node_length];exact current
  have first:=ByteWindow.packet memory entry [] (headerBytes mode entry)
    (LittleEndian.wordEncode 4 symbol++pointerBytes mode (backEntry mode entry) back++pointerBytes mode (forwardEntry mode entry) forward)
    (by simpa only [List.nil_append,List.append_assoc] using packet)
  have last:=ByteWindow.packet memory entry (headerBytes mode entry++LittleEndian.wordEncode 4 symbol)
    (pointerBytes mode (backEntry mode entry) back++pointerBytes mode (forwardEntry mode entry) forward) []
    (by simpa only [List.append_nil] using packet)
  refine ⟨by simpa only [List.length_nil,Nat.add_zero,prefix_length] using first,?_⟩
  simpa only [List.length_append,prefix_length,LittleEndian.word_encode_length,pointer_length,Nat.two_mul] using last

/-- A preserved header/pointer suffix and the actual live symbol determine
the complete current node packet; no later packet is assumed. -/
theorem current (mode : Mode) (entry : Nat) (symbol : BitVec 32) (back forward : Word mode)
    (memory : ByteMemory.Memory)
    (header : ByteMemory.bytesAt memory entry 6=headerBytes mode entry)
    (pointers : ByteMemory.bytesAt memory (entry+10) (2*pointerSpan mode)=
      pointerBytes mode (backEntry mode entry) back++pointerBytes mode (forwardEntry mode entry) forward)
    (value : DwordCode.get memory (entry+6)=symbol) :
    ByteMemory.bytesAt memory entry (nodeSpan mode)=nodeBytes mode entry symbol back forward := by
  rw [shape]
  have first:=ByteWindow.join memory entry (headerBytes mode entry) (LittleEndian.wordEncode 4 symbol)
    (by simpa only [prefix_length] using header)
    (by simpa only [prefix_length,LittleEndian.word_encode_length] using symbol_bytes memory entry symbol value)
  have whole:=ByteWindow.join memory entry (headerBytes mode entry++LittleEndian.wordEncode 4 symbol)
    (pointerBytes mode (backEntry mode entry) back++pointerBytes mode (forwardEntry mode entry) forward) first
    (by simpa only [List.length_append,prefix_length,LittleEndian.word_encode_length,pointer_length,Nat.two_mul] using pointers)
  simpa only [List.length_append,prefix_length,LittleEndian.word_encode_length,pointer_length,nodeSpan,Nat.two_mul] using whole

theorem initial_from_packets (mode : Mode) (start : Nat) (items : List (Listing8NodeBlock.Values mode))
    (memory : ByteMemory.Memory)
    (each : ∀ index value,items[index]?=some value →
      ByteMemory.bytesAt memory (Listing8NodeTable.entryPC mode start index) (nodeSpan mode)=
        Listing8NodeBlock.bytes mode (Listing8NodeTable.entryPC mode start index) value) :
    Listing8NodeTable.Initial mode start items memory := by
  induction items generalizing start with
  | nil => rfl
  | cons value items ih =>
    have first:=each 0 value rfl
    simp only [Listing8NodeTable.entryPC,Nat.zero_mul,Nat.add_zero] at first
    have rest : Listing8NodeTable.Initial mode (start+nodeSpan mode) items memory := by
      apply ih
      intro index item found
      have packet:=each (index+1) item (by simpa only [List.getElem?_cons_succ] using found)
      have address : Listing8NodeTable.entryPC mode start (index+1)=Listing8NodeTable.entryPC mode (start+nodeSpan mode) index := by
        dsimp [Listing8NodeTable.entryPC];rw [Nat.add_mul,Nat.one_mul];omega
      rw [address] at packet
      exact packet
    change ByteMemory.bytesAt memory start (Listing8NodeBlock.bytes mode start value++
      Listing8NodeTable.bytes mode (start+nodeSpan mode) items).length=_
    apply ByteWindow.join
    · simpa only [Listing8NodeBlock.bytes,node_length] using first
    · simpa only [Listing8NodeTable.Initial,Listing8NodeBlock.bytes,node_length] using rest
end SmcTuring.Appendix.Listing8LiveNodePacket

module
public import SmcTuring.Appendix.Listing9ExecutionImage

public section
namespace SmcTuring.Appendix.Listing9MetadataPackets
open Native Listing9PackedLayout

/-- The epilogue's final exchange rewrites the original zero save operand to
its own complete field address. All emitted header bytes are retained. -/
theorem save_current (mode : Mode) (start transitions nodes : Nat) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (ByteMemory.putWord mode (Listing9Image.memory mode start transitions nodes backing)
      (layout mode start transitions nodes).save (Arithmetic.encodeNat mode (layout mode start transitions nodes).save))
      (saveOwner mode start transitions nodes) (StringCodec.initialSize mode)=
      StringInit.bytes mode (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save := by
  let original:=Listing9Image.memory mode start transitions nodes backing
  let owner:=saveOwner mode start transitions nodes
  let field:=(layout mode start transitions nodes).save
  have current:=Listing9Image.save_current mode start transitions nodes backing
  have existing : ByteMemory.bytesAt original owner ((StringInit.leading mode owner)++LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode 0)).length=
      StringInit.leading mode owner++LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode 0) := by
    rw [←StringInit.initial_shape,StringInit.bytes,StringCodec.initial_length]
    exact current
  have patched:=ByteMemory.patch_payload original owner (StringInit.leading mode owner)
    (LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode 0)) (LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode field))
    (by rw [LittleEndian.word_encode_length,LittleEndian.word_encode_length])
  rw [ByteMemory.put_current original owner _ existing,StringInit.leading_length,←StringInit.initial_shape mode owner field] at patched
  change ByteMemory.putWord mode original field (Arithmetic.encodeNat mode field)=ByteMemory.putBytes original owner (StringInit.bytes mode owner field) at patched
  rw [patched]
  simpa only [StringInit.bytes,StringCodec.initial_length] using ByteMemory.bytes_at_put original owner (StringInit.bytes mode owner field)

theorem pointer_current (mode : Mode) (start transitions nodes : Nat) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (ByteMemory.putWord mode (Listing9Image.memory mode start transitions nodes backing)
      (layout mode start transitions nodes).save (Arithmetic.encodeNat mode (layout mode start transitions nodes).save))
      (pointerOwner mode start transitions nodes) (StringCodec.initialSize mode)=
      StringInit.bytes mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save := by
  rw [StackWindows.word_window _ _ _ _ _ _ (Or.inl (Nat.le_of_eq (positions mode start transitions nodes).2.2.2.1))]
  exact Listing9Image.pointer_current mode start transitions nodes backing

theorem save_value (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes) (backing : ByteMemory.Memory) :
    Execution.load mode (ByteMemory.putWord mode (Listing9Image.memory mode start transitions nodes backing)
      (layout mode start transitions nodes).save (Arithmetic.encodeNat mode (layout mode start transitions nodes).save))
      (Arithmetic.encodeNat mode (layout mode start transitions nodes).save)=Arithmetic.encodeNat mode (layout mode start transitions nodes).save :=
  StringInit.initialized_pointer mode (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save _
    (owner_capacity mode start transitions nodes bounds).1 (save_current mode start transitions nodes backing)

end SmcTuring.Appendix.Listing9MetadataPackets

module
public import SmcTuring.Native.PairedPayloadTemplate
public import SmcTuring.Native.StringMacroLayout

public section
namespace SmcTuring.Native.StringMacroTemplates
open LittleEndian StringMacroLayout

@[expose] def front (mode : Mode) (p : Params) : List Byte := StringInit.leading mode p.start
@[expose] def middle (mode : Mode) (p : Params) : List Byte :=
  StringCodec.exchangeBytes mode false (p.start+StringCodec.initialSize mode) (StringCodec.sourceField mode p.start) ++
    StringInit.leading mode (StringCodec.destinationStart mode p.start)
@[expose] def last (mode : Mode) (p : Params) : List Byte :=
  let tail := StringCodec.bodyEnd mode p.start p.size
  let exchange := StringCodec.exchangeSize mode
  let subtract := StringCodec.subSize mode p.size
  StringCodec.exchangeBytes mode true (StringCodec.destinationStart mode p.start+StringCodec.initialSize mode)
      (StringCodec.destinationField mode p.start) ++ StringPlan.bytes mode p.size ++
    StringCodec.exchangeBytes mode false tail (StringCodec.sourceField mode p.start) ++
    StringCodec.subBytes mode (tail+exchange) (StringCodec.sourceField mode p.start) p.size ++
    StringCodec.exchangeBytes mode true (tail+exchange+subtract) (StringCodec.destinationField mode p.start) ++
    StringCodec.subBytes mode (tail+2*exchange+subtract) (StringCodec.destinationField mode p.start) p.size

@[expose] def Intact (mode : Mode) (p : Params) (memory : ByteMemory.Memory) : Prop :=
  PairedPayloadTemplate.Intact mode memory p.start (front mode p) (middle mode p) (last mode p)

theorem shape (mode : Mode) (p : Params) :
    bytes mode p = front mode p ++ wordEncode mode.wordBytes (Arithmetic.encodeNat mode p.source) ++
      middle mode p ++ wordEncode mode.wordBytes (Arithmetic.encodeNat mode p.destination) ++ last mode p := by
  have a : StringCodec.initialBytes mode p.start (StringCodec.sourceField mode p.start) p.source =
      StringInit.leading mode p.start++wordEncode mode.wordBytes (Arithmetic.encodeNat mode p.source) :=
    StringInit.initial_shape mode p.start p.source
  have b : StringCodec.initialBytes mode (StringCodec.destinationStart mode p.start)
      (StringCodec.destinationField mode p.start) p.destination =
      StringInit.leading mode (StringCodec.destinationStart mode p.start)++wordEncode mode.wordBytes (Arithmetic.encodeNat mode p.destination) :=
    StringInit.initial_shape mode (StringCodec.destinationStart mode p.start) p.destination
  rw [bytes,StringCodec.bytes,a,b]
  simp only [front,middle,last,List.append_assoc]

theorem fields (mode : Mode) (p : Params) :
    PairedPayloadTemplate.firstField p.start (front mode p) = StringCodec.sourceField mode p.start ∧
    PairedPayloadTemplate.secondField mode p.start (front mode p) (middle mode p) = StringCodec.destinationField mode p.start := by
  simp only [PairedPayloadTemplate.firstField,PairedPayloadTemplate.secondField,front,middle,
    List.length_append,StringInit.leading_length,StringCodec.exchange_length]
  have h := StringCodec.field_end mode p.start
  simp only [StringCodec.sourceField] at h
  simp only [StringCodec.sourceField,StringCodec.destinationField,StringCodec.destinationStart]
  exact ⟨True.intro,by omega⟩

theorem extent (mode : Mode) (p : Params) :
    PairedPayloadTemplate.span mode (front mode p) (middle mode p) (last mode p) = endpoint mode p-p.start := by
  have h := congrArg List.length (shape mode p)
  simp only [bytes,StringCodec.whole_length,List.length_append,word_encode_length] at h
  exact h.symm

theorem initial (mode : Mode) (p : Params) (memory : ByteMemory.Memory)
    (present : ByteMemory.bytesAt memory p.start (bytes mode p).length=bytes mode p) : Intact mode p memory := by
  rw [shape] at present
  exact PairedPayloadTemplate.initial mode memory p.start (front mode p) (middle mode p) (last mode p) _ _ present

/-- The whole original macro encoding is reconstructed from the two live
cursor words. Source/destination values may be temporary saved registers. -/
theorem current (mode : Mode) (p : Params) (memory : ByteMemory.Memory) (intact : Intact mode p memory) :
    let live : Params := {p with
      source := (Protected.wordAt mode memory (StringCodec.sourceField mode p.start)).toNat,
      destination := (Protected.wordAt mode memory (StringCodec.destinationField mode p.start)).toNat}
    ByteMemory.bytesAt memory p.start (bytes mode live).length=bytes mode live := by
  dsimp only
  have h := PairedPayloadTemplate.current mode memory p.start (front mode p) (middle mode p) (last mode p) intact
  rw [(fields mode p).1,(fields mode p).2] at h
  simp only [shape,List.length_append,word_encode_length]
  simpa only [PairedPayloadTemplate.span,front,middle,last,Arithmetic.encodeNat,BitVec.ofNat_toNat,BitVec.setWidth_eq] using h

theorem operand_store (mode : Mode) (p : Params) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List Byte) (intact : Intact mode p memory)
    (owned : (StringCodec.sourceField mode p.start≤address ∧ address+packet.length≤StringCodec.sourceField mode p.start+mode.wordBytes) ∨
      (StringCodec.destinationField mode p.start≤address ∧ address+packet.length≤StringCodec.destinationField mode p.start+mode.wordBytes)) :
    Intact mode p (ByteMemory.putBytes memory address packet) := by
  apply PairedPayloadTemplate.operand_store mode memory p.start (front mode p) (middle mode p) (last mode p) address packet intact
  simpa only [(fields mode p).1,(fields mode p).2] using owned

theorem frame (mode : Mode) (p : Params) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List Byte) (intact : Intact mode p memory)
    (outside : address+packet.length≤p.start ∨ endpoint mode p≤address) :
    Intact mode p (ByteMemory.putBytes memory address packet) := by
  apply PairedPayloadTemplate.frame mode memory p.start (front mode p) (middle mode p) (last mode p) address packet intact
  rw [extent]
  have bounds := field_coordinates mode p
  rcases outside with before | after
  · exact Or.inl before
  · exact Or.inr (by omega)

theorem buffer_store (mode : Mode) (p : Params) (memory : ByteMemory.Memory)
    (buffer address : Nat) (packet : List Byte) (intact : Intact mode p memory)
    (outside : Outside mode p buffer)
    (inside : buffer≤address ∧ address+packet.length≤buffer+max p.size mode.wordBytes) :
    Intact mode p (ByteMemory.putBytes memory address packet) := by
  apply frame mode p memory address packet intact
  rcases outside with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end SmcTuring.Native.StringMacroTemplates

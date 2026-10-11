module
public import SmcTuring.Native.StringEncodedTemplates

public section
namespace SmcTuring.Native.StringInitTemplates

@[expose] def Intact (mode : Mode) (start : Nat) (memory : ByteMemory.Memory) : Prop :=
  PayloadTemplate.Prefix memory start (StringInit.leading mode start)

theorem extent (mode : Mode) (start : Nat) :
    (StringInit.leading mode start).length+mode.wordBytes=StringCodec.initialSize mode := by
  rw [StringInit.leading_length]
  cases mode <;> rfl

theorem initial (mode : Mode) (start value : Nat) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory start (StringCodec.initialSize mode)=StringInit.bytes mode start value) :
    Intact mode start memory := by
  have packet : ByteMemory.bytesAt memory start
      (StringInit.leading mode start++LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode value)).length=
      StringInit.leading mode start++LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode value) := by
    rw [List.length_append,LittleEndian.word_encode_length,extent,←StringInit.initial_shape]
    exact current
  exact StringWindow.packet_window memory start [] (StringInit.leading mode start)
    (LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode value)) (by simpa only [List.nil_append] using packet)

theorem current (mode : Mode) (start : Nat) (memory : ByteMemory.Memory) (intact : Intact mode start memory) :
    ByteMemory.bytesAt memory start (StringCodec.initialSize mode)=
      StringInit.bytes mode start (Protected.wordAt mode memory (StringInit.field mode start)).toNat := by
  have packet := PayloadTemplate.current mode memory start (StringInit.leading mode start) intact
  rw [extent,StringInit.leading_length] at packet
  rw [StringInit.initial_shape]
  simpa only [StringInit.field,Arithmetic.encodeNat,BitVec.ofNat_toNat,BitVec.setWidth_eq] using packet

theorem lengths (mode : Mode) (start old fresh : Nat) :
    StringEncodedTemplates.lengths mode (StringInit.forms mode start old)=
      StringEncodedTemplates.lengths mode (StringInit.forms mode start fresh) := by
  cases mode <;> simp [StringEncodedTemplates.lengths,StringInit.forms,StringForm.encode,Native.encode,Appendix.ByteCode.encode]

theorem legal (mode : Mode) (start value : Nat) :
    ∀ form∈StringInit.forms mode start value,StringForm.Legal mode form := by
  cases mode <;> simp [StringInit.forms,StringForm.Legal]

@[expose] def Decodes (mode : Mode) (start : Nat) (memory : ByteMemory.Memory) : Prop :=
  ∀ index,index<(StringInit.forms mode start 0).length →
    ∃ form,StringForm.Legal mode form ∧
      StringStack.fetch mode memory (start+StringEncodedTemplates.offset mode (StringInit.forms mode start 0) index)=
        some (StringWrites.liftString mode form)

theorem decodes (mode : Mode) (start : Nat) (memory : ByteMemory.Memory) (intact : Intact mode start memory) :
    Decodes mode start memory := by
  intro index small
  let forms := StringInit.forms mode start (Protected.wordAt mode memory (StringInit.field mode start)).toNat
  have sameLengths := lengths mode start 0 (Protected.wordAt mode memory (StringInit.field mode start)).toNat
  have sameCount : (StringInit.forms mode start 0).length=forms.length := by
    have h := congrArg List.length sameLengths
    simpa only [StringEncodedTemplates.lengths,List.length_map] using h
  have bound : index<forms.length := by rw [←sameCount];exact small
  have image : ByteMemory.bytesAt memory start (StringEncodedTemplates.encoding mode forms).length=
      StringEncodedTemplates.encoding mode forms := by
    rw [StringEncodedTemplates.encoding,StringInit.forms_encoding]
    simpa only [StringInit.bytes,StringCodec.initial_length] using current mode start memory intact
  have fetched := StringEncodedTemplates.fetch_index mode memory start forms index bound (legal mode start _) image
  have sameOffset : StringEncodedTemplates.offset mode (StringInit.forms mode start 0) index=
      StringEncodedTemplates.offset mode forms index := by simp only [StringEncodedTemplates.offset_sum,sameLengths,forms]
  exact ⟨forms[index],legal mode start _ _ (List.getElem_mem bound),by rw [sameOffset];exact fetched⟩

theorem frame (mode : Mode) (start : Nat) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : Intact mode start memory)
    (outside : address+packet.length≤start ∨ StringInit.field mode start≤address) :
    Intact mode start (ByteMemory.putBytes memory address packet) := by
  apply PayloadTemplate.frame memory start (StringInit.leading mode start) address packet intact
  intro index inside
  have bound : index.val<StringCodec.fieldOffset mode := by simpa only [StringInit.leading_length] using index.isLt
  unfold ByteMemory.Inside at inside
  simp only [StringInit.field] at outside
  rcases outside with before | after <;> omega

end SmcTuring.Native.StringInitTemplates

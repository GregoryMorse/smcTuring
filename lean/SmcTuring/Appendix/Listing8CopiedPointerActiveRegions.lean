module
public import SmcTuring.Appendix.Listing8OwnerTemplateCollection
public import SmcTuring.Appendix.Listing8OriginalPointerTemplates
public import SmcTuring.Native.JointTemplateStates

public section
namespace SmcTuring.Appendix.Listing8CopiedPointerActiveRegions
open Native Listing8Prototypes Listing8CopiedPointer Listing8OwnerTemplateCollection

/-- Only the actual complete self operand or dereferenced word can be active.
An empty region records positively proved restoration. -/
@[expose] def Allowed (mode : Mode) (source copied : Nat) (value : Word mode) (packet : StringWrites.Packet) : Prop :=
  packet.bytes=[] ∨ (packet.address=selfField mode source copied ∨ packet.address=value.toNat) ∧
    packet.bytes.length=mode.wordBytes
@[expose] def Certificate (mode : Mode) (source copied : Nat) (value : Word mode)
    (templates : List (Template mode)) (initial memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,Allowed mode source copied value packet ∧
    memory=ByteMemory.putBytes initial packet.address packet.bytes ∧
    ∀ template∈templates,Listing8OwnerTemplateCollection.Outside mode template packet →
      Listing8OwnerTemplateCollection.Intact mode template memory ∧ Listing8OwnerTemplateCollection.Decodes mode template memory

theorem packet_certificate (mode : Mode) (source copied : Nat) (value : Word mode)
    (templates : List (Template mode)) (memory : ByteMemory.Memory)
    (current : All mode templates memory) (packet : StringWrites.Packet) (allowed : Allowed mode source copied value packet) :
    Certificate mode source copied value templates memory (ByteMemory.putBytes memory packet.address packet.bytes) := by
  refine ⟨packet,allowed,rfl,?_⟩
  intro template member outside
  have kept:=Listing8OwnerTemplateCollection.store_outside mode templates memory current packet template member outside
  exact ⟨kept,Listing8OwnerTemplateCollection.decodes mode template _ kept⟩

theorem unchanged (mode : Mode) (source copied : Nat) (value : Word mode)
    (templates : List (Template mode)) (memory : ByteMemory.Memory) (current : All mode templates memory) :
    Certificate mode source copied value templates memory memory := by
  have empty : ByteMemory.putBytes memory 0 []=memory := by
    funext position;simp [ByteMemory.putBytes,ByteMemory.Inside]
  simpa only [empty] using packet_certificate mode source copied value templates memory current ⟨0,[]⟩ (Or.inl rfl)

/-- Both temporary architectural word writes and both restorations are
derived from the actual four reader instructions and present physical words. -/
theorem run (mode : Mode) (source copied : Nat) (value : Word mode)
    (templates : List (Template mode)) (state : StringExecution.State mode)
    (current : All mode templates state.principal.memory)
    (entry : state.principal.pc=Arithmetic.encodeNat mode copied)
    (sourceFits : source+pointerSpan mode<2^(8*mode.wordBytes))
    (copiedFits : copied+pointerSpan mode<2^(8*mode.wordBytes))
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory source (pointerBytes mode source value).length=pointerBytes mode source value)
    (copiedCurrent : ByteMemory.bytesAt state.principal.memory copied (pointerBytes mode source value).length=pointerBytes mode source value) :
    StringTemplateStates.Run mode (fun reached => Certificate mode source copied value templates state.principal.memory reached.principal.memory)
      ((forms mode source copied value).map (StringWrites.liftString mode)) state := by
  let one:=StringExecution.execute mode (.native (first mode source copied)) state
  let two:=StringExecution.execute mode (.native (second mode source copied)) one
  let three:=StringExecution.execute mode (.native .exchangeIndirect) two
  let four:=StringExecution.execute mode (.native (.moffs value)) three
  have pointer:=self_value mode source copied value state.principal.memory sourceFits copiedFits sourceCurrent copiedCurrent
  have firstHits:=first_hits mode source copied state.principal entry
  have secondHits:=second_hits mode source copied state.principal entry
  have fieldFits : selfField mode source copied<2^(8*mode.wordBytes) := by
    cases mode <;> simp [selfField,pointerField,Listing8CopiedPointer.origin,pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset,Mode.wordBytes]
      at sourceFits copiedFits ⊢ <;> omega
  have mem1 : one.principal.memory=ByteMemory.putWord mode state.principal.memory (selfField mode source copied) state.principal.accumulator := by
    have e:=congrArg Execution.State.memory (Reader.exchange_effect mode state.principal (label mode source copied) _ firstHits)
    change one.principal.memory=ByteMemory.putWord mode state.principal.memory (Arithmetic.encodeNat mode (selfField mode source copied)).toNat state.principal.accumulator at e
    rw [Arithmetic.encode_nat_toNat mode _ fieldFits] at e
    exact e
  have mem2 : two.principal.memory=state.principal.memory := Reader.restored_memory mode state.principal _ _ _ firstHits secondHits
  have mem3 : three.principal.memory=ByteMemory.putWord mode state.principal.memory value.toNat value := by
    have e:=Reader.dereferenced_memory mode state.principal _ _ _ firstHits secondHits
    rw [pointer] at e;exact e
  have mem4 : four.principal.memory=state.principal.memory := by
    change (finish mode source copied value state).principal.memory=state.principal.memory
    rw [effect mode source copied value state entry pointer]
  have kept0:=unchanged mode source copied value templates state.principal.memory current
  have kept1 : Certificate mode source copied value templates state.principal.memory one.principal.memory := by
    rw [mem1]
    exact packet_certificate mode source copied value templates state.principal.memory current
      ⟨selfField mode source copied,LittleEndian.wordEncode mode.wordBytes state.principal.accumulator⟩
      (Or.inr ⟨Or.inl rfl,LittleEndian.word_encode_length _ _⟩)
  have kept2 : Certificate mode source copied value templates state.principal.memory two.principal.memory := by rw [mem2];exact kept0
  have kept3 : Certificate mode source copied value templates state.principal.memory three.principal.memory := by
    rw [mem3]
    exact packet_certificate mode source copied value templates state.principal.memory current
      ⟨value.toNat,LittleEndian.wordEncode mode.wordBytes value⟩ (Or.inr ⟨Or.inr rfl,LittleEndian.word_encode_length _ _⟩)
  have kept4 : Certificate mode source copied value templates state.principal.memory four.principal.memory := by rw [mem4];exact kept0
  change Certificate mode source copied value templates state.principal.memory state.principal.memory ∧
    Certificate mode source copied value templates state.principal.memory one.principal.memory ∧
    Certificate mode source copied value templates state.principal.memory two.principal.memory ∧
    Certificate mode source copied value templates state.principal.memory three.principal.memory ∧
    Certificate mode source copied value templates state.principal.memory four.principal.memory
  exact ⟨kept0,kept1,kept2,kept3,kept4⟩

theorem own_template (mode : Mode) (source copied : Nat) (value : Word mode)
    (templates : List (Template mode)) (state : StringExecution.State mode)
    (current : All mode templates state.principal.memory)
    (entry : state.principal.pc=Arithmetic.encodeNat mode copied)
    (sourceFits : source+pointerSpan mode<2^(8*mode.wordBytes)) (copiedFits : copied+pointerSpan mode<2^(8*mode.wordBytes))
    (sourcePlaced : source=copied ∨ source+pointerSpan mode≤copied ∨ copied+pointerSpan mode≤source)
    (targetOutside : value.toNat+mode.wordBytes≤copied ∨ copied+pointerSpan mode≤value.toNat)
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory source (pointerBytes mode source value).length=pointerBytes mode source value)
    (copiedCurrent : ByteMemory.bytesAt state.principal.memory copied (pointerBytes mode source value).length=pointerBytes mode source value) :
    StringTemplateStates.Run mode (fun reached =>
      Certificate mode source copied value templates state.principal.memory reached.principal.memory ∧
      Listing8PointerTemplate.Intact mode source copied reached.principal.memory ∧
      Listing8OwnerTemplateCollection.Decodes mode (.pointer source copied) reached.principal.memory)
      ((forms mode source copied value).map (StringWrites.liftString mode)) state := by
  have own:=Listing8OriginalPointerTemplates.run mode source copied value state entry sourceFits copiedFits sourcePlaced targetOutside sourceCurrent copiedCurrent
  exact StringTemplateStates.monotone mode _ _ _ state
    (fun reached kept => ⟨kept.1,kept.2,Listing8PointerTemplate.decodes mode source copied reached.principal.memory kept.2⟩)
    (JointTemplateStates.join mode _ _ _ state
      (run mode source copied value templates state current entry sourceFits copiedFits sourceCurrent copiedCurrent) own)

end SmcTuring.Appendix.Listing8CopiedPointerActiveRegions

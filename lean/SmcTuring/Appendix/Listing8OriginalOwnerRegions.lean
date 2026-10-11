module
public import SmcTuring.Appendix.Listing8OwnerTemplateCollection
public import SmcTuring.Appendix.Listing8OriginalPointerTemplates
public import SmcTuring.Appendix.Listing8OriginalOwnerWrites

public section
namespace SmcTuring.Appendix.Listing8OriginalOwnerRegions
open Native Listing8Prototypes Listing8OriginalOwners

/-- A transient region is empty, the original pointer's own complete operand,
or the exact word at its initially encoded referent. It cannot be enlarged to
hide a previous write or an unrelated invalid template. -/
@[expose] def Allowed (mode : Mode) (owners : List (Owner mode)) (packet : StringWrites.Packet) :=
  packet.bytes=[] ∨ ∃ pc value,.pointer pc value∈owners ∧
    (packet.address=pointerField mode pc ∨ packet.address=value.toNat) ∧ packet.bytes.length=mode.wordBytes
@[expose] def Certificate (mode : Mode) (owners : List (Owner mode))
    (initial memory : ByteMemory.Memory) :=
  ∃ packet : StringWrites.Packet,Allowed mode owners packet ∧
    memory=ByteMemory.putBytes initial packet.address packet.bytes ∧
    ∀ template∈owners.map (Listing8OwnerTemplateCollection.original mode),
      Listing8OwnerTemplateCollection.Outside mode template packet →
      Listing8OwnerTemplateCollection.Intact mode template memory

theorem packet_certificate (mode : Mode) (owners : List (Owner mode)) (memory : ByteMemory.Memory)
    (current : Intact mode owners memory) (packet : StringWrites.Packet) (allowed : Allowed mode owners packet) :
    Certificate mode owners memory (ByteMemory.putBytes memory packet.address packet.bytes) :=
  ⟨packet,allowed,rfl,Listing8OwnerTemplateCollection.store_outside mode _ memory
    (Listing8OwnerTemplateCollection.original_current mode owners memory current) packet⟩

theorem unchanged (mode : Mode) (owners : List (Owner mode)) (memory : ByteMemory.Memory)
    (current : Intact mode owners memory) : Certificate mode owners memory memory := by
  have kept : ByteMemory.putBytes memory 0 []=memory := by
    funext position
    simp [ByteMemory.putBytes,ByteMemory.Inside]
  simpa only [kept] using packet_certificate mode owners memory current ⟨0,[]⟩ (Or.inl rfl)

/-- Both temporary word exchanges have their actual complete architectural
windows; restoration empties the region after the second and fourth steps. -/
theorem pointer_run (mode : Mode) (owners : List (Owner mode)) (pc : Nat) (value : Word mode)
    (member : .pointer pc value∈owners) (valid : Valid mode (.pointer pc value))
    (memory : ByteMemory.Memory) (current : Intact mode owners memory) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc) (initial : state.principal.memory=memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode owners memory reached.principal.memory)
      ((Listing8CopiedPointer.forms mode pc pc value).map (StringWrites.liftString mode)) state := by
  let one := StringExecution.execute mode (.native (Listing8CopiedPointer.first mode pc pc)) state
  let two := StringExecution.execute mode (.native (Listing8CopiedPointer.second mode pc pc)) one
  let three := StringExecution.execute mode (.native .exchangeIndirect) two
  let four := StringExecution.execute mode (.native (.moffs value)) three
  have packet : ByteMemory.bytesAt state.principal.memory pc (pointerBytes mode pc value).length=pointerBytes mode pc value := by
    rw [initial];exact current _ member
  have pointer := Listing8CopiedPointer.self_value mode pc pc value state.principal.memory valid.1 valid.1 packet packet
  have firstHits := Listing8CopiedPointer.first_hits mode pc pc state.principal entry
  have secondHits := Listing8CopiedPointer.second_hits mode pc pc state.principal entry
  have fieldFits : pointerField mode pc<2^(8*mode.wordBytes) := by
    have bound := valid.1
    cases mode <;> simp [pointerField,pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset,Mode.wordBytes] at * <;> omega
  have field_eq : Listing8CopiedPointer.selfField mode pc pc=pointerField mode pc := by cases mode <;> rfl
  have mem1 : one.principal.memory=ByteMemory.putWord mode memory (pointerField mode pc) state.principal.accumulator := by
    have e := congrArg Execution.State.memory (Reader.exchange_effect mode state.principal
      (Listing8CopiedPointer.label mode pc pc) _ firstHits)
    change one.principal.memory=ByteMemory.putWord mode state.principal.memory
      (Arithmetic.encodeNat mode (Listing8CopiedPointer.selfField mode pc pc)).toNat state.principal.accumulator at e
    rw [field_eq,Arithmetic.encode_nat_toNat mode _ fieldFits,initial] at e
    exact e
  have mem2 : two.principal.memory=memory := by
    rw [show two.principal.memory=state.principal.memory from
      Reader.restored_memory mode state.principal _ _ _ firstHits secondHits,initial]
  have mem3 : three.principal.memory=ByteMemory.putWord mode memory value.toNat value := by
    have e := Reader.dereferenced_memory mode state.principal _ _ _ firstHits secondHits
    rw [pointer,initial] at e
    exact e
  have mem4 : four.principal.memory=memory := by
    change (Listing8CopiedPointer.finish mode pc pc value state).principal.memory=memory
    rw [Listing8CopiedPointer.effect mode pc pc value state entry pointer,initial]
  have kept0 : Certificate mode owners memory state.principal.memory := by rw [initial];exact unchanged mode owners memory current
  have kept1 : Certificate mode owners memory one.principal.memory := by
    rw [mem1]
    exact packet_certificate mode owners memory current
      ⟨pointerField mode pc,LittleEndian.wordEncode mode.wordBytes state.principal.accumulator⟩
      (Or.inr ⟨pc,value,member,Or.inl rfl,LittleEndian.word_encode_length _ _⟩)
  have kept2 : Certificate mode owners memory two.principal.memory := by rw [mem2];exact unchanged mode owners memory current
  have kept3 : Certificate mode owners memory three.principal.memory := by
    rw [mem3]
    exact packet_certificate mode owners memory current
      ⟨value.toNat,LittleEndian.wordEncode mode.wordBytes value⟩
      (Or.inr ⟨pc,value,member,Or.inr rfl,LittleEndian.word_encode_length _ _⟩)
  have kept4 : Certificate mode owners memory four.principal.memory := by rw [mem4];exact unchanged mode owners memory current
  change Certificate mode owners memory state.principal.memory ∧
    Certificate mode owners memory one.principal.memory ∧ Certificate mode owners memory two.principal.memory ∧
    Certificate mode owners memory three.principal.memory ∧ Certificate mode owners memory four.principal.memory
  exact ⟨kept0,kept1,kept2,kept3,kept4⟩

theorem advance_run (mode : Mode) (owners : List (Owner mode)) (owner : Owner mode)
    (member : owner∈owners) (valid : Valid mode owner) (memory : ByteMemory.Memory)
    (current : Intact mode owners memory) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner)) (initial : state.principal.memory=memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode owners memory reached.principal.memory)
      ((forms mode owner).map (StringStoreWrites.liftDword mode)) state := by
  cases owner with
  | pointer pc value =>
    have mapped : ((forms mode (.pointer pc value)).map (StringStoreWrites.liftDword mode))=
      (Listing8CopiedPointer.forms mode pc pc value).map (StringWrites.liftString mode) := by
      rw [forms,List.map_map];rfl
    rw [mapped]
    exact pointer_run mode owners pc value member valid memory current state entry initial
  | scalar pc value =>
    have packet : Current mode (.scalar pc value) state.principal.memory := by rw [initial];exact current _ member
    have effect := advance_effect mode (.scalar pc value) state valid entry packet
    have kept0 : Certificate mode owners memory state.principal.memory := by rw [initial];exact unchanged mode owners memory current
    have kept1 : Certificate mode owners memory (advance mode (.scalar pc value) state).principal.memory := by
      rw [effect,initial];exact unchanged mode owners memory current
    exact ⟨kept0,kept1⟩

/-- Arbitrary finite original declaration sequences keep all executable owner
templates valid outside one precise contiguous transient word. At each owner
boundary that region is empty; it never accumulates across the sequence. -/
theorem run_fragment (mode : Mode) (owners remaining : List (Owner mode)) (start : Nat)
    (included : ∀ owner∈remaining,owner∈owners) (chain : Contiguous mode start remaining)
    (valid : ∀ owner∈remaining,Valid mode owner) (memory : ByteMemory.Memory)
    (current : Intact mode owners memory) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start) (initial : state.principal.memory=memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode owners memory reached.principal.memory)
      ((program mode remaining).map (StringStoreWrites.liftDword mode)) state := by
  induction remaining generalizing start state with
  | nil =>
    change Certificate mode owners memory state.principal.memory
    rw [initial];exact unchanged mode owners memory current
  | cons owner remaining ih =>
    have v := valid owner (List.Mem.head _)
    have member := included owner (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner) := by rw [chain.1];exact entry
    have packet : Current mode owner state.principal.memory := by rw [initial];exact current owner member
    have first := advance_run mode owners owner member v memory current state location initial
    have effect := advance_effect mode owner state v location packet
    have next : (advance mode owner state).principal.pc=Arithmetic.encodeNat mode (pc mode owner+span mode owner) := by rw [effect]
    have nextMemory : (advance mode owner state).principal.memory=memory := by rw [effect,initial]
    have rest := ih _ (fun owner member => included owner (List.Mem.tail _ member)) chain.2
      (fun owner member => valid owner (List.Mem.tail _ member)) _ next nextMemory
    rw [program,List.flatMap_cons,List.map_append,StringTemplateStates.append,
      Listing8OriginalOwnerWrites.advance_run mode owner state v location packet]
    exact ⟨first,rest⟩

theorem at_prefix (mode : Mode) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (current : Intact mode owners state.principal.memory) (before after : List (StringStack.Form mode))
    (cut : (program mode owners).map (StringStoreWrites.liftDword mode)=before++after) :
    Certificate mode owners state.principal.memory (StringWrites.run mode before state).principal.memory := by
  have allStates := run_fragment mode owners owners start (fun _ member => member) chain valid
    state.principal.memory current state entry rfl
  rw [cut] at allStates
  exact StringTemplateStates.at_prefix mode _ before after state allStates

theorem region_inside (mode : Mode) (owners : List (Owner mode)) (codeStart codeEnd : Nat)
    (placed : ∀ owner∈owners,Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner)
    (packet : StringWrites.Packet) (allowed : Allowed mode owners packet) :
    packet.bytes=[] ∨ codeStart≤packet.address ∧ packet.address+packet.bytes.length≤codeEnd := by
  rcases allowed with empty | ⟨pc,value,member,location,length⟩
  · exact Or.inl empty
  · right
    have position := placed _ member
    rw [length]
    rcases location with field | referent
    · rw [field]
      have bounds := Listing8OwnerTemplateCollection.field_bounds mode (.pointer pc pc)
      change pc≤pointerField mode pc ∧ pointerField mode pc+mode.wordBytes=pc+pointerSpan mode at bounds
      exact ⟨Nat.le_trans position.1.1 bounds.1,by rw [bounds.2];exact position.1.2⟩
    · rw [referent];exact position.2

end SmcTuring.Appendix.Listing8OriginalOwnerRegions

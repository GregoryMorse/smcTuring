module
public import SmcTuring.Appendix.Listing8PointerTemplate
public import SmcTuring.Appendix.Listing8ScalarTemplate
public import SmcTuring.Appendix.Listing8OwnerSequence
public import SmcTuring.Appendix.Listing8OriginalOwners

public section
namespace SmcTuring.Appendix.Listing8OwnerTemplateCollection
open Native Listing8Prototypes

/-- Static original encoding geometry; mutable operand values are absent. -/
inductive Template (mode : Mode) where
  | pointer (source copied : Nat)
  | scalar (pc : Nat) (displacement : BitVec 32)
  deriving DecidableEq
@[expose] def start (mode : Mode) : Template mode → Nat
  | .pointer _ copied => copied
  | .scalar pc _ => pc
@[expose] def span (mode : Mode) : Template mode → Nat
  | .pointer _ _ => pointerSpan mode
  | .scalar _ _ => 10
@[expose] def field (mode : Mode) : Template mode → Nat
  | .pointer _ copied => pointerField mode copied
  | .scalar pc _ => pc+6
@[expose] def width (mode : Mode) : Template mode → Nat
  | .pointer _ _ => mode.wordBytes
  | .scalar _ _ => 4
@[expose] def Intact (mode : Mode) (template : Template mode) (memory : ByteMemory.Memory) : Prop :=
  match template with
  | .pointer source copied => Listing8PointerTemplate.Intact mode source copied memory
  | .scalar pc d => Listing8ScalarTemplate.Intact pc d memory
@[expose] def All (mode : Mode) (templates : List (Template mode)) (memory : ByteMemory.Memory) :=
  ∀ template∈templates,Intact mode template memory
@[expose] def Apart (mode : Mode) (first second : Template mode) :=
  start mode first+span mode first≤start mode second ∨ start mode second+span mode second≤start mode first
@[expose] def Separated (mode : Mode) (templates : List (Template mode)) :=
  ∀ first∈templates,∀ second∈templates,first≠second → Apart mode first second
@[expose] def Operand (mode : Mode) (template : Template mode) (packet : StringWrites.Packet) :=
  field mode template≤packet.address ∧ packet.address+packet.bytes.length≤field mode template+width mode template
@[expose] def Owned (mode : Mode) (templates : List (Template mode)) (packet : StringWrites.Packet) :=
  ∃ template∈templates,Operand mode template packet
@[expose] def Outside (mode : Mode) (template : Template mode) (packet : StringWrites.Packet) :=
  packet.address+packet.bytes.length≤start mode template ∨ start mode template+span mode template≤packet.address
@[expose] def Decodes (mode : Mode) (template : Template mode) (memory : ByteMemory.Memory) : Prop :=
  match template with
  | .pointer source copied =>
      let live := Protected.wordAt mode memory (pointerField mode copied)
      StringStack.fetch mode memory copied=some (StringWrites.liftNative mode (Listing8CopiedPointer.first mode source copied)) ∧
      StringStack.fetch mode memory (copied+ReaderImage.firstSize mode)=
        some (StringWrites.liftNative mode (Listing8CopiedPointer.second mode source copied)) ∧
      StringStack.fetch mode memory (copied+ReaderImage.firstSize mode+ReaderImage.secondSize mode)=
        some (StringWrites.liftNative mode .exchangeIndirect) ∧
      StringStack.fetch mode memory (copied+ReaderImage.prefixSize mode)=some (StringWrites.liftNative mode (.moffs live))
  | .scalar pc d => StringStack.fetch mode memory pc=some (StringStoreWrites.liftDword mode
      (StringDword.store mode d (Protected.wordAt .x86 memory (pc+6))))

theorem decodes (mode : Mode) (template : Template mode) (memory : ByteMemory.Memory)
    (intact : Intact mode template memory) : Decodes mode template memory := by
  cases template with
  | pointer source copied => exact Listing8PointerTemplate.decodes mode source copied memory intact
  | scalar pc d => exact Listing8ScalarTemplate.decodes mode pc d memory intact

theorem field_bounds (mode : Mode) (template : Template mode) :
    start mode template≤field mode template ∧ field mode template+width mode template=start mode template+span mode template := by
  cases template with
  | pointer source copied =>
    cases mode <;> simp [start,field,width,span,pointerField,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize,Mode.wordBytes,Nat.add_assoc]
  | scalar pc d => simp [start,field,width,span,Nat.add_assoc]

theorem operand_store (mode : Mode) (template : Template mode) (memory : ByteMemory.Memory)
    (intact : Intact mode template memory) (packet : StringWrites.Packet) (operand : Operand mode template packet) :
    Intact mode template (ByteMemory.putBytes memory packet.address packet.bytes) := by
  have upper := operand.2
  rw [(field_bounds mode template).2] at upper
  cases template with
  | pointer source copied => exact Listing8PointerTemplate.operand_store mode source copied memory intact _ _ operand.1 upper
  | scalar pc d => exact Listing8ScalarTemplate.operand_store pc d memory intact _ _ operand.1 upper

theorem frame (mode : Mode) (template : Template mode) (memory : ByteMemory.Memory)
    (intact : Intact mode template memory) (packet : StringWrites.Packet) (outside : Outside mode template packet) :
    Intact mode template (ByteMemory.putBytes memory packet.address packet.bytes) := by
  cases template with
  | pointer source copied => exact Listing8PointerTemplate.frame mode source copied memory intact _ _ outside
  | scalar pc d => exact Listing8ScalarTemplate.frame pc d memory intact _ _ outside

theorem operand_apart (mode : Mode) (writer observed : Template mode) (packet : StringWrites.Packet)
    (operand : Operand mode writer packet) (apart : Apart mode writer observed) : Outside mode observed packet := by
  have lower := (field_bounds mode writer).1
  have upper := operand.2
  rw [(field_bounds mode writer).2] at upper
  unfold Apart at apart
  unfold Outside
  rcases apart with before | after
  · left;omega
  · right;have placed := operand.1;omega

/-- A packet inside any listed complete operand preserves every executable
owner template. Membership and separation describe initial static geometry. -/
theorem store_all (mode : Mode) (templates : List (Template mode)) (memory : ByteMemory.Memory)
    (separate : Separated mode templates) (intact : All mode templates memory)
    (packet : StringWrites.Packet) (owned : Owned mode templates packet) :
    All mode templates (ByteMemory.putBytes memory packet.address packet.bytes) := by
  rcases owned with ⟨writer,member,operand⟩
  intro observed observedMember
  by_cases same : writer=observed
  · subst observed;exact operand_store mode writer memory (intact writer member) packet operand
  · exact frame mode observed memory (intact observed observedMember) packet
      (operand_apart mode writer observed packet operand (separate writer member observed observedMember same))

/-- A temporary header-touching exchange preserves every template wholly
outside its exact single contiguous architectural modification window. -/
theorem store_outside (mode : Mode) (templates : List (Template mode)) (memory : ByteMemory.Memory)
    (intact : All mode templates memory) (packet : StringWrites.Packet) :
    ∀ template∈templates,Outside mode template packet →
      Intact mode template (ByteMemory.putBytes memory packet.address packet.bytes) := by
  intro template member outside
  exact frame mode template memory (intact template member) packet outside

@[expose] def original (mode : Mode) : Listing8OriginalOwners.Owner mode → Template mode
  | .pointer pc _ => .pointer pc pc
  | .scalar pc _ => .scalar pc (Relocation.memoryDisp mode (pc+10) (pc+6))
@[expose] def copied (mode : Mode) : Listing8OwnerSequence.Owner mode → Template mode
  | .pointer source pc _ => .pointer source pc
  | .scalar pc target _ => .scalar pc (Relocation.memoryDisp mode (pc+10) target)

theorem original_current (mode : Mode) (owners : List (Listing8OriginalOwners.Owner mode)) (memory : ByteMemory.Memory)
    (current : Listing8OriginalOwners.Intact mode owners memory) :
    All mode (owners.map (original mode)) memory := by
  intro template member
  rcases List.mem_map.mp member with ⟨owner,ownerMember,rfl⟩
  have ready := current owner ownerMember
  cases owner with
  | pointer pc value => exact Listing8PointerTemplate.initial mode pc pc value memory ready
  | scalar pc value => exact Listing8ScalarTemplate.original mode pc value memory ready

theorem copied_current (mode : Mode) (owners : List (Listing8OwnerSequence.Owner mode)) (memory : ByteMemory.Memory)
    (current : Listing8OwnerSequence.Intact mode owners memory) :
    All mode (owners.map (copied mode)) memory := by
  intro template member
  rcases List.mem_map.mp member with ⟨owner,ownerMember,rfl⟩
  have ready := current owner ownerMember
  cases owner with
  | pointer source pc value => exact Listing8PointerTemplate.initial mode source pc value memory ready.2
  | scalar pc target value => exact Listing8ScalarTemplate.initial pc _ value memory ready

end SmcTuring.Appendix.Listing8OwnerTemplateCollection

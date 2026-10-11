module
public import SmcTuring.Appendix.Listing8RetargetPointerOwners

public section
namespace SmcTuring.Appendix.Listing8PhaseOwnerCatalog
open Native Listing8CopyImage Listing8Prototypes Listing8OwnerTemplateCollection
/-- The scalar descriptor records the exact current displacement DWORD.
Pointer source/copy geometry remains the exact original geometry. -/
@[expose] def live (mode : Mode) (template : Template mode) (memory : ByteMemory.Memory) : Template mode :=
  match template with
  | .pointer source copied => .pointer source copied
  | .scalar pc _ => .scalar pc (DwordCode.get memory (pc+2))
@[expose] def All (mode : Mode) (owners : List (Listing8OwnerSequence.Owner mode)) (memory : ByteMemory.Memory) : Prop :=
  ∀ template∈Listing8CopiedOwnerCatalog.catalog mode owners,
    Intact mode (live mode template memory) memory ∧ Decodes mode (live mode template memory) memory
@[expose] def Certificate (mode : Mode) (owners : List (Listing8OwnerSequence.Owner mode)) (memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,Listing8CopiedOwnerActiveRun.Allowed mode owners packet ∧
    ∀ template∈Listing8CopiedOwnerCatalog.catalog mode owners,Outside mode template packet →
      Intact mode (live mode template memory) memory ∧ Decodes mode (live mode template memory) memory

theorem scalar_current (mode : Mode) (pc : Nat) (memory : ByteMemory.Memory)
    (intact : DwordOperandTemplates.Intact .store pc memory) :
    Listing8ScalarTemplate.Intact pc (DwordCode.get memory (pc+2)) memory ∧
      StringStack.fetch mode memory pc=some (StringStoreWrites.liftDword mode
        (StringDword.store mode (DwordCode.get memory (pc+2)) (Protected.wordAt .x86 memory (pc+6)))) := by
  have head:=Listing8ScalarTemplate.initial pc _ _ memory (DwordOperandTemplates.current .store pc memory intact)
  exact ⟨head,Listing8ScalarTemplate.decodes mode pc _ memory head⟩

theorem from_fixed (mode : Mode) (template : Template mode) (memory : ByteMemory.Memory)
    (intact : Intact mode template memory) :
    Intact mode (live mode template memory) memory ∧ Decodes mode (live mode template memory) memory := by
  cases template with
  | pointer source copied => exact ⟨intact,Listing8PointerTemplate.decodes mode source copied memory intact⟩
  | scalar pc displacement =>
    exact scalar_current mode pc memory
      (DwordOperandTemplates.initial .store pc displacement (Protected.wordAt .x86 memory (pc+6)) memory
        (Listing8ScalarTemplate.current pc displacement memory intact))

theorem from_catalogs (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory)
    (pointers : Listing8OwnerTemplateCollection.All mode (Listing8RetargetPointerOwners.templates mode l) memory)
    (scalars : DwordTemplateCollection.All (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) memory) :
    All mode (Listing8OwnerImage.owners mode l v) memory := by
  have pointer : ∀ source copied,Template.pointer source copied∈Listing8RetargetPointerOwners.templates mode l →
      Intact mode (.pointer source copied) memory ∧ Decodes mode (.pointer source copied) memory :=
    fun source copied member => ⟨pointers _ member,Listing8PointerTemplate.decodes mode source copied memory (pointers _ member)⟩
  have scalar : ∀ pc displacement,DwordTemplateCollection.Template.binary .store pc∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l) →
      Intact mode (live mode (.scalar pc displacement) memory) memory ∧ Decodes mode (live mode (.scalar pc displacement) memory) memory :=
    fun pc _ member => scalar_current mode pc memory (scalars _ member)
  intro template member
  simp only [Listing8CopiedOwnerCatalog.catalog,Listing8OwnerImage.owners,Listing8CopiedOwnerCatalog.entries,
    List.flatMap_cons,List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | rfl | rfl | rfl | (rfl | rfl)
  all_goals first
    | exact pointer _ _ (by simp [Listing8RetargetPointerOwners.templates])
    | exact scalar _ _ (by simp [Listing8RetargetExecutableTemplates.templates,Listing8ModeOffsets.sites,
        transitionParams,patchLayout,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry])

theorem empty (mode : Mode) (owners : List (Listing8OwnerSequence.Owner mode)) (memory : ByteMemory.Memory)
    (current : All mode owners memory) : Certificate mode owners memory :=
  ⟨⟨0,[]⟩,Or.inl rfl,fun template member _ => current template member⟩

theorem from_fixed_certificate (mode : Mode) (owners : List (Listing8OwnerSequence.Owner mode)) (memory : ByteMemory.Memory)
    (current : Listing8CopiedOwnerActiveRun.Certificate mode owners memory) : Certificate mode owners memory := by
  obtain ⟨packet,allowed,headers⟩:=current
  exact ⟨packet,allowed,fun template member outside => from_fixed mode template memory (headers template member outside).1⟩

end SmcTuring.Appendix.Listing8PhaseOwnerCatalog

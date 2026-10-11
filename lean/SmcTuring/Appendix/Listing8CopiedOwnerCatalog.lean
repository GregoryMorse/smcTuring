module
public import SmcTuring.Appendix.Listing8CopiedPointerActiveRegions

public section
namespace SmcTuring.Appendix.Listing8CopiedOwnerCatalog
open Native Listing8Prototypes Listing8OwnerSequence Listing8OwnerTemplateCollection

/-- Every copied pointer retains both its original-source and physical-copy
executable descriptors. Scalar descriptors use the actual relocated target. -/
@[expose] def entries (mode : Mode) : Owner mode → List (Template mode)
  | .pointer source copied _ => [.pointer source source,.pointer source copied]
  | .scalar pc target _ => [.scalar pc (Relocation.memoryDisp mode (pc+10) target)]
@[expose] def catalog (mode : Mode) (owners : List (Owner mode)) := owners.flatMap (entries mode)

theorem current (mode : Mode) (owner : Owner mode) (memory : ByteMemory.Memory)
    (present : Listing8OwnerSequence.Current mode owner memory) : All mode (entries mode owner) memory := by
  cases owner with
  | pointer source copied value =>
    intro template member
    simp only [entries,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Listing8PointerTemplate.initial mode source source value memory present.1
    · exact Listing8PointerTemplate.initial mode source copied value memory present.2
  | scalar pc target value =>
    intro template member
    simp only [entries,List.mem_singleton] at member
    subst template
    apply Listing8ScalarTemplate.initial pc (Relocation.memoryDisp mode (pc+10) target) value memory
    exact present

theorem all_current (mode : Mode) (owners : List (Owner mode)) (memory : ByteMemory.Memory)
    (present : Listing8OwnerSequence.Intact mode owners memory) : All mode (catalog mode owners) memory := by
  intro template member
  obtain ⟨owner,inOwners,inEntry⟩:=List.mem_flatMap.mp member
  exact current mode owner memory (present owner inOwners) template inEntry

theorem window (mode : Mode) (owner : Owner mode) (template : Template mode) (member : template∈entries mode owner) :
    (Listing8OwnerTemplateCollection.start mode template,Listing8OwnerTemplateCollection.span mode template)∈Listing8OwnerSequence.windows mode owner := by
  cases owner with
  | pointer source copied value =>
    simp only [entries,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · simp only [Listing8OwnerSequence.windows,Listing8OwnerTemplateCollection.start,Listing8OwnerTemplateCollection.span,pointer_length,List.mem_cons,List.not_mem_nil,or_false]
      exact Or.inl trivial
    · simp only [Listing8OwnerSequence.windows,Listing8OwnerTemplateCollection.start,Listing8OwnerTemplateCollection.span,pointer_length,List.mem_cons,List.not_mem_nil,or_false]
      exact Or.inr trivial
  | scalar pc target value =>
    simp only [entries,List.mem_singleton] at member
    subst template
    exact List.mem_singleton.mpr rfl

/-- A scalar owner's actual store leaves every listed source/copy executable
packet fixed. Pointer readers restore the whole memory positively. -/
theorem retained (mode : Mode) (owners : List (Owner mode)) (writer : Owner mode)
    (state : StringExecution.State mode) (valid : Valid mode writer)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8OwnerSequence.pc mode writer))
    (present : Listing8OwnerSequence.Current mode writer state.principal.memory)
    (outside : ∀ reader∈owners,Listing8OwnerSequence.Outside mode writer reader)
    (intact : All mode (catalog mode owners) state.principal.memory) :
    All mode (catalog mode owners) (advance mode writer state).principal.memory := by
  cases writer with
  | pointer source copied value =>
    rw [pointer_effect mode source copied value state valid entry present]
    exact intact
  | scalar pc target value =>
    rw [scalar_effect mode pc target value state valid entry]
    intro template member
    obtain ⟨reader,inOwners,inEntry⟩:=List.mem_flatMap.mp member
    apply Listing8OwnerTemplateCollection.frame mode template state.principal.memory (intact template member)
      ⟨target,LittleEndian.wordEncode 4 value⟩
    simpa only [Listing8OwnerTemplateCollection.Outside,LittleEndian.word_encode_length] using
      outside reader inOwners _ (window mode reader template inEntry)

end SmcTuring.Appendix.Listing8CopiedOwnerCatalog

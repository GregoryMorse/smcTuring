module
public import SmcTuring.Appendix.Listing8OriginalGraphOwnerInitial

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphOwnerRun
open Native Listing8Prototypes Listing8SourceGraph Listing8OwnerSequence
attribute [local irreducible] StringTemplateStates.Run
@[expose] def ScalarSafe (mode : Mode) (origin : Nat) : Owner mode → Prop
  | .pointer _ _ _ => True
  | .scalar _ target _ => target+4≤Listing8FullTableImage.start mode origin
@[expose] def Certificate (mode : Mode) (origin : Nat) (g : Graph) (owners : List (Owner mode)) (memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,Listing8CopiedOwnerActiveRun.Allowed mode owners packet ∧
    ∀ template∈Listing8CopiedOwnerCatalog.catalog mode owners++Listing8OriginalGraphCatalog.catalog mode origin g,
      Listing8OwnerTemplateCollection.Outside mode template packet →
      Listing8OwnerTemplateCollection.Intact mode template memory ∧ Listing8OwnerTemplateCollection.Decodes mode template memory

theorem empty (mode : Mode) (origin : Nat) (g : Graph) (owners : List (Owner mode)) (memory : ByteMemory.Memory)
    (copied : Listing8OwnerTemplateCollection.All mode (Listing8CopiedOwnerCatalog.catalog mode owners) memory)
    (originals : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory) : Certificate mode origin g owners memory := by
  refine ⟨⟨0,[]⟩,Or.inl rfl,?_⟩
  intro template member _
  have intact : Listing8OwnerTemplateCollection.Intact mode template memory := by
    rcases List.mem_append.mp member with copy | original
    · exact copied template copy
    · exact originals template original
  exact ⟨intact,Listing8OwnerTemplateCollection.decodes mode template memory intact⟩

theorem retained_originals (mode : Mode) (origin : Nat) (g : Graph) (owner : Owner mode)
    (safe : ScalarSafe mode origin owner) (state : StringExecution.State mode) (valid : Valid mode owner)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner))
    (present : Current mode owner state.principal.memory)
    (originals : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) (advance mode owner state).principal.memory := by
  cases owner with
  | pointer source copied value =>
    rw [pointer_effect mode source copied value state valid entry present]
    exact originals
  | scalar pc target value =>
    rw [scalar_effect mode pc target value state valid entry]
    exact Listing8OriginalGraphFailureRun.store mode origin g _ target (LittleEndian.wordEncode 4 value) originals (by
      rw [LittleEndian.word_encode_length];exact safe)

theorem advance (mode : Mode) (origin : Nat) (g : Graph) (owners : List (Owner mode)) (owner : Owner mode)
    (member : owner∈owners) (safe : ScalarSafe mode origin owner) (state : StringExecution.State mode) (valid : Valid mode owner)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner)) (present : Current mode owner state.principal.memory)
    (outside : ∀ reader∈owners,Listing8OwnerSequence.Outside mode owner reader)
    (copied : Listing8OwnerTemplateCollection.All mode (Listing8CopiedOwnerCatalog.catalog mode owners) state.principal.memory)
    (originals : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode origin g owners reached.principal.memory)
      ((forms mode owner).map (StringStoreWrites.liftDword mode)) state := by
  cases owner with
  | pointer source copiedPC value =>
    have all : Listing8OwnerTemplateCollection.All mode
        (Listing8CopiedOwnerCatalog.catalog mode owners++Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory := by
      intro template inside
      rcases List.mem_append.mp inside with copy | original
      · exact copied template copy
      · exact originals template original
    have mapping : ((Listing8CopiedPointer.forms mode source copiedPC value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)=
        (Listing8CopiedPointer.forms mode source copiedPC value).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
    change StringTemplateStates.Run mode _
      (((Listing8CopiedPointer.forms mode source copiedPC value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)) state
    rw [mapping]
    exact StringTemplateStates.monotone mode _ _ _ state (fun reached current => by
      obtain ⟨packet,allowed,_,headers⟩:=current
      refine ⟨packet,?_,headers⟩
      rcases allowed with restored | ⟨addresses,size⟩
      · exact Or.inl restored
      · exact Or.inr ⟨source,copiedPC,value,member,addresses,size⟩)
      (Listing8CopiedPointerActiveRegions.run mode source copiedPC value _ state all entry valid.1 valid.2.1 present.1 present.2)
  | scalar pc target value =>
    have kept:=Listing8CopiedOwnerCatalog.retained mode owners (.scalar pc target value) state valid entry present outside copied
    have graph:=retained_originals mode origin g (.scalar pc target value) safe state valid entry present originals
    simp only [forms,List.map_cons,List.map_nil,StringTemplateStates.Run]
    change Certificate mode origin g owners state.principal.memory ∧
      Certificate mode origin g owners (Listing8OwnerSequence.advance mode (.scalar pc target value) state).principal.memory
    exact ⟨empty mode origin g owners _ copied originals,empty mode origin g owners _ kept graph⟩

theorem run_fragment (mode : Mode) (origin : Nat) (g : Graph) (owners remaining : List (Owner mode)) (start : Nat)
    (subset : ∀ owner∈remaining,owner∈owners) (chain : Contiguous mode start remaining)
    (valid : ∀ owner∈remaining,Valid mode owner)
    (outside : ∀ writer∈remaining,∀ reader∈owners,Listing8OwnerSequence.Outside mode writer reader)
    (safe : ∀ owner∈remaining,ScalarSafe mode origin owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (present : Listing8OwnerSequence.Intact mode remaining state.principal.memory)
    (copied : Listing8OwnerTemplateCollection.All mode (Listing8CopiedOwnerCatalog.catalog mode owners) state.principal.memory)
    (originals : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode origin g owners reached.principal.memory)
      ((program mode remaining).map (StringStoreWrites.liftDword mode)) state := by
  induction remaining generalizing start state with
  | nil =>
    rw [program,List.flatMap_nil,List.map_nil,StringTemplateStates.Run]
    exact empty mode origin g owners _ copied originals
  | cons owner remaining ih =>
    have v:=valid owner (List.Mem.head _)
    have c:=present owner (List.Mem.head _)
    have s:=safe owner (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner) := by rw [chain.1];exact entry
    have first:=advance mode origin g owners owner (subset owner (List.Mem.head _)) s state v location c (outside owner (List.Mem.head _)) copied originals
    have next:=advance_pc mode owner state v location c
    have retained : Listing8OwnerSequence.Intact mode remaining (Listing8OwnerSequence.advance mode owner state).principal.memory := by
      intro reader member
      exact Listing8OwnerSequence.retained mode owner reader state v location c (present reader (List.mem_cons_of_mem _ member))
        (outside owner (List.Mem.head _) reader (subset reader (List.mem_cons_of_mem _ member)))
    have copies:=Listing8CopiedOwnerCatalog.retained mode owners owner state v location c (outside owner (List.Mem.head _)) copied
    have graph:=retained_originals mode origin g owner s state v location c originals
    have later:=ih (pc mode owner+span mode owner) (fun reader member => subset reader (List.mem_cons_of_mem _ member)) chain.2
      (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer member => outside writer (List.mem_cons_of_mem _ member))
      (fun reader member => safe reader (List.mem_cons_of_mem _ member)) _ next retained copies graph
    rw [program,List.flatMap_cons,List.map_append,StringTemplateStates.append,
      Listing8OwnerSequenceWrites.advance_run mode owner state v location c]
    exact ⟨first,later⟩

theorem run (mode : Mode) (origin : Nat) (g : Graph) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (outside : ∀ writer∈owners,∀ reader∈owners,Listing8OwnerSequence.Outside mode writer reader)
    (safe : ∀ owner∈owners,ScalarSafe mode origin owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (present : Listing8OwnerSequence.Intact mode owners state.principal.memory)
    (originals : Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode origin g owners reached.principal.memory)
      ((program mode owners).map (StringStoreWrites.liftDword mode)) state :=
  run_fragment mode origin g owners owners start (fun _ member => member) chain valid outside safe state entry present
    (Listing8CopiedOwnerCatalog.all_current mode owners state.principal.memory present) originals

end SmcTuring.Appendix.Listing8OriginalGraphOwnerRun

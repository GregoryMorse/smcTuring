module
public import SmcTuring.Appendix.Listing8CopiedOwnerCatalog
public import SmcTuring.Appendix.Listing8OwnerSequenceWrites

public section
namespace SmcTuring.Appendix.Listing8CopiedOwnerActiveRun
open Native Listing8Prototypes Listing8OwnerSequence Listing8OwnerTemplateCollection
attribute [local irreducible] StringTemplateStates.Run

@[expose] def Allowed (mode : Mode) (owners : List (Owner mode)) (packet : StringWrites.Packet) : Prop :=
  packet.bytes=[] ∨ ∃ source copied value,.pointer source copied value∈owners ∧
    (packet.address=Listing8CopiedPointer.selfField mode source copied ∨ packet.address=value.toNat) ∧
    packet.bytes.length=mode.wordBytes
@[expose] def Certificate (mode : Mode) (owners : List (Owner mode)) (memory : ByteMemory.Memory) : Prop :=
  ∃ packet : StringWrites.Packet,Allowed mode owners packet ∧
    ∀ template∈Listing8CopiedOwnerCatalog.catalog mode owners,
      Listing8OwnerTemplateCollection.Outside mode template packet →
      Listing8OwnerTemplateCollection.Intact mode template memory ∧ Listing8OwnerTemplateCollection.Decodes mode template memory

theorem empty (mode : Mode) (owners : List (Owner mode)) (memory : ByteMemory.Memory)
    (current : All mode (Listing8CopiedOwnerCatalog.catalog mode owners) memory) : Certificate mode owners memory := by
  refine ⟨⟨0,[]⟩,Or.inl rfl,?_⟩
  intro template member _
  exact ⟨current template member,Listing8OwnerTemplateCollection.decodes mode template memory (current template member)⟩

theorem pointer_certificate (mode : Mode) (owners : List (Owner mode)) (source copied : Nat) (value : Word mode)
    (member : .pointer source copied value∈owners) (initial memory : ByteMemory.Memory)
    (exactRegion : Listing8CopiedPointerActiveRegions.Certificate mode source copied value
      (Listing8CopiedOwnerCatalog.catalog mode owners) initial memory) : Certificate mode owners memory := by
  obtain ⟨packet,allowed,_,kept⟩:=exactRegion
  refine ⟨packet,?_,kept⟩
  rcases allowed with restored | ⟨address,size⟩
  · exact Or.inl restored
  · exact Or.inr ⟨source,copied,value,member,address,size⟩

/-- At each actual reader boundary only its complete operand/referent word
may be active; both restorations empty it. Scalars preserve all owner headers. -/
theorem advance (mode : Mode) (owners : List (Owner mode)) (owner : Owner mode) (member : owner∈owners)
    (state : StringExecution.State mode) (valid : Valid mode owner)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8OwnerSequence.pc mode owner))
    (present : Listing8OwnerSequence.Current mode owner state.principal.memory)
    (outside : ∀ reader∈owners,Listing8OwnerSequence.Outside mode owner reader)
    (current : All mode (Listing8CopiedOwnerCatalog.catalog mode owners) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode owners reached.principal.memory)
      ((forms mode owner).map (StringStoreWrites.liftDword mode)) state := by
  cases owner with
  | pointer source copied value =>
    have mapping : ((Listing8CopiedPointer.forms mode source copied value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)=
        (Listing8CopiedPointer.forms mode source copied value).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
    change StringTemplateStates.Run mode _
      (((Listing8CopiedPointer.forms mode source copied value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)) state
    rw [mapping]
    exact StringTemplateStates.monotone mode _ _ _ state
      (fun reached exactRegion => pointer_certificate mode owners source copied value member state.principal.memory reached.principal.memory exactRegion)
      (Listing8CopiedPointerActiveRegions.run mode source copied value _ state current entry valid.1 valid.2.1 present.1 present.2)
  | scalar pc target value =>
    have kept:=Listing8CopiedOwnerCatalog.retained mode owners (.scalar pc target value) state valid entry present outside current
    simp only [forms,List.map_cons,List.map_nil,StringTemplateStates.Run]
    change Certificate mode owners state.principal.memory ∧
      Certificate mode owners (Listing8OwnerSequence.advance mode (.scalar pc target value) state).principal.memory
    exact ⟨empty mode owners state.principal.memory current,empty mode owners _ kept⟩

theorem run_fragment (mode : Mode) (owners remaining : List (Owner mode)) (start : Nat)
    (subset : ∀ owner∈remaining,owner∈owners) (chain : Contiguous mode start remaining)
    (valid : ∀ owner∈remaining,Valid mode owner)
    (outside : ∀ writer∈remaining,∀ reader∈owners,Listing8OwnerSequence.Outside mode writer reader)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (present : Listing8OwnerSequence.Intact mode remaining state.principal.memory)
    (current : All mode (Listing8CopiedOwnerCatalog.catalog mode owners) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode owners reached.principal.memory)
      ((program mode remaining).map (StringStoreWrites.liftDword mode)) state := by
  induction remaining generalizing start state with
  | nil =>
    change StringTemplateStates.Run mode _ [] state
    rw [StringTemplateStates.Run]
    exact empty mode owners _ current
  | cons owner remaining ih =>
    have v:=valid owner (List.Mem.head _)
    have c:=present owner (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode (Listing8OwnerSequence.pc mode owner) := by rw [chain.1];exact entry
    have first:=advance mode owners owner (subset owner (List.Mem.head _)) state v location c (outside owner (List.Mem.head _)) current
    have next:=advance_pc mode owner state v location c
    have retained : Listing8OwnerSequence.Intact mode remaining (Listing8OwnerSequence.advance mode owner state).principal.memory := by
      intro reader member
      exact Listing8OwnerSequence.retained mode owner reader state v location c (present reader (List.mem_cons_of_mem _ member))
        (outside owner (List.Mem.head _) reader (subset reader (List.mem_cons_of_mem _ member)))
    have kept:=Listing8CopiedOwnerCatalog.retained mode owners owner state v location c (outside owner (List.Mem.head _)) current
    have later:=ih (Listing8OwnerSequence.pc mode owner+Listing8OwnerSequence.span mode owner)
      (fun reader member => subset reader (List.mem_cons_of_mem _ member)) chain.2
      (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer member => outside writer (List.mem_cons_of_mem _ member)) _ next retained kept
    rw [program,List.flatMap_cons,List.map_append,StringTemplateStates.append,
      Listing8OwnerSequenceWrites.advance_run mode owner state v location c]
    exact ⟨first,later⟩

theorem run (mode : Mode) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (outside : ∀ writer∈owners,∀ reader∈owners,Listing8OwnerSequence.Outside mode writer reader)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (present : Listing8OwnerSequence.Intact mode owners state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Certificate mode owners reached.principal.memory)
      ((program mode owners).map (StringStoreWrites.liftDword mode)) state :=
  run_fragment mode owners owners start (fun _ member => member) chain valid outside state entry present
    (Listing8CopiedOwnerCatalog.all_current mode owners state.principal.memory present)

end SmcTuring.Appendix.Listing8CopiedOwnerActiveRun

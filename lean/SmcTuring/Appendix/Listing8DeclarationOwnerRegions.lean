module
public import SmcTuring.Appendix.Listing8DeclarationOwnerGeometry
public import SmcTuring.Appendix.Listing8OriginalOwnerRegions
public import SmcTuring.Appendix.Listing8DeclarationWrites

public section
namespace SmcTuring.Appendix.Listing8DeclarationOwnerRegions
open Native Listing8DeclarationOwnerGeometry

/-- Complete actual original nodes declarations, including every transient
word exchange. Current source bytes and static bounds are the only inputs. -/
theorem nodes (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode))
    (valid : Listing8NodeTable.Valid mode start table) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Listing8NodeTable.Initial mode start table state.principal.memory) :
    StringDword.Trace mode state (Listing8NodeTrace.program mode start table) (Listing8NodeTrace.finish mode start table state) ∧
    StringTemplateStates.Run mode
      (fun reached => Listing8OriginalOwnerRegions.Certificate mode (Listing8NodeTable.owners mode start table)
        state.principal.memory reached.principal.memory)
      ((Listing8NodeTrace.program mode start table).map (StringStoreWrites.liftDword mode)) state := by
  have allStates := Listing8OriginalOwnerRegions.run_fragment mode (Listing8NodeTable.owners mode start table)
    (Listing8NodeTable.owners mode start table) start (fun _ member => member) (nodes_chain mode start table)
    (nodes_valid mode start table valid) state.principal.memory (nodes_current mode start table _ initial) state entry rfl
  rw [nodes_program] at allStates
  exact ⟨Listing8NodeTrace.trace mode start table valid state entry initial,allStates⟩

theorem nodes_prefix (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode))
    (valid : Listing8NodeTable.Valid mode start table) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Listing8NodeTable.Initial mode start table state.principal.memory)
    (before after : List (StringStack.Form mode))
    (cut : (Listing8NodeTrace.program mode start table).map (StringStoreWrites.liftDword mode)=before++after) :
    Listing8OriginalOwnerRegions.Certificate mode (Listing8NodeTable.owners mode start table) state.principal.memory
      (StringWrites.run mode before state).principal.memory := by
  have allStates := (nodes mode start table valid state entry initial).2
  rw [cut] at allStates
  exact StringTemplateStates.at_prefix mode _ before after state allStates

/-- Complete actual original transitions declarations, including every transient
word exchange. Current source bytes and static bounds are the only inputs. -/
theorem transitions (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode))
    (valid : Listing8TransitionTable.Valid mode start table) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Listing8TransitionTable.Initial mode start table state.principal.memory) :
    StringDword.Trace mode state (Listing8TableTrace.program mode start table) (Listing8TableTrace.finish mode start table state) ∧
    StringTemplateStates.Run mode
      (fun reached => Listing8OriginalOwnerRegions.Certificate mode (Listing8TransitionTable.owners mode start table)
        state.principal.memory reached.principal.memory)
      ((Listing8TableTrace.program mode start table).map (StringStoreWrites.liftDword mode)) state := by
  have allStates := Listing8OriginalOwnerRegions.run_fragment mode (Listing8TransitionTable.owners mode start table)
    (Listing8TransitionTable.owners mode start table) start (fun _ member => member) (transitions_chain mode start table)
    (transitions_valid mode start table valid) state.principal.memory (transitions_current mode start table _ initial) state entry rfl
  rw [transitions_program] at allStates
  exact ⟨Listing8TableTrace.trace mode start table valid state entry initial,allStates⟩

theorem transitions_prefix (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode))
    (valid : Listing8TransitionTable.Valid mode start table) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Listing8TransitionTable.Initial mode start table state.principal.memory)
    (before after : List (StringStack.Form mode))
    (cut : (Listing8TableTrace.program mode start table).map (StringStoreWrites.liftDword mode)=before++after) :
    Listing8OriginalOwnerRegions.Certificate mode (Listing8TransitionTable.owners mode start table) state.principal.memory
      (StringWrites.run mode before state).principal.memory := by
  have allStates := (transitions mode start table valid state entry initial).2
  rw [cut] at allStates
  exact StringTemplateStates.at_prefix mode _ before after state allStates

theorem nodes_placed (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode)) (codeStart codeEnd : Nat)
    (placed : Listing8DeclarationWrites.NodePlaced mode codeStart codeEnd start table) :
    ∀ owner∈Listing8NodeTable.owners mode start table,Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner := by
  induction table generalizing start with
  | nil => intro owner member;simp only [Listing8NodeTable.owners,List.not_mem_nil] at member
  | cons value table ih =>
    intro owner member
    rw [Listing8NodeTable.owners,List.mem_append] at member
    rcases member with first | later
    · exact placed.1 owner first
    · exact ih _ placed.2 owner later

/-- Every actual prefix has one exact in-code transient region and full
current decoding of every original template wholly outside that region. -/
theorem nodes_checked_prefix (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode))
    (valid : Listing8NodeTable.Valid mode start table) (codeStart codeEnd : Nat)
    (placed : Listing8DeclarationWrites.NodePlaced mode codeStart codeEnd start table)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Listing8NodeTable.Initial mode start table state.principal.memory)
    (before after : List (StringStack.Form mode))
    (cut : (Listing8NodeTrace.program mode start table).map (StringStoreWrites.liftDword mode)=before++after) :
    let reached := StringWrites.run mode before state
    ∃ packet : StringWrites.Packet,
      Listing8OriginalOwnerRegions.Allowed mode (Listing8NodeTable.owners mode start table) packet ∧
      reached.principal.memory=ByteMemory.putBytes state.principal.memory packet.address packet.bytes ∧
      (packet.bytes=[] ∨ codeStart≤packet.address ∧ packet.address+packet.bytes.length≤codeEnd) ∧
      ∀ template∈(Listing8NodeTable.owners mode start table).map (Listing8OwnerTemplateCollection.original mode),
        Listing8OwnerTemplateCollection.Outside mode template packet →
        Listing8OwnerTemplateCollection.Intact mode template reached.principal.memory ∧
        Listing8OwnerTemplateCollection.Decodes mode template reached.principal.memory := by
  rcases nodes_prefix mode start table valid state entry initial before after cut with ⟨packet,allowed,memory,kept⟩
  refine ⟨packet,allowed,memory,Listing8OriginalOwnerRegions.region_inside mode _ codeStart codeEnd
    (nodes_placed mode start table codeStart codeEnd placed) packet allowed,?_⟩
  intro template member outside
  have intact := kept template member outside
  exact ⟨intact,Listing8OwnerTemplateCollection.decodes mode template _ intact⟩

theorem transitions_placed (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode)) (codeStart codeEnd : Nat)
    (placed : Listing8DeclarationWrites.TransitionPlaced mode codeStart codeEnd start table) :
    ∀ owner∈Listing8TransitionTable.owners mode start table,Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner := by
  induction table generalizing start with
  | nil => intro owner member;simp only [Listing8TransitionTable.owners,List.not_mem_nil] at member
  | cons value table ih =>
    intro owner member
    rw [Listing8TransitionTable.owners,List.mem_append] at member
    rcases member with first | later
    · exact placed.1 owner first
    · exact ih _ placed.2 owner later

/-- Every actual prefix has one exact in-code transient region and full
current decoding of every original template wholly outside that region. -/
theorem transitions_checked_prefix (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode))
    (valid : Listing8TransitionTable.Valid mode start table) (codeStart codeEnd : Nat)
    (placed : Listing8DeclarationWrites.TransitionPlaced mode codeStart codeEnd start table)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Listing8TransitionTable.Initial mode start table state.principal.memory)
    (before after : List (StringStack.Form mode))
    (cut : (Listing8TableTrace.program mode start table).map (StringStoreWrites.liftDword mode)=before++after) :
    let reached := StringWrites.run mode before state
    ∃ packet : StringWrites.Packet,
      Listing8OriginalOwnerRegions.Allowed mode (Listing8TransitionTable.owners mode start table) packet ∧
      reached.principal.memory=ByteMemory.putBytes state.principal.memory packet.address packet.bytes ∧
      (packet.bytes=[] ∨ codeStart≤packet.address ∧ packet.address+packet.bytes.length≤codeEnd) ∧
      ∀ template∈(Listing8TransitionTable.owners mode start table).map (Listing8OwnerTemplateCollection.original mode),
        Listing8OwnerTemplateCollection.Outside mode template packet →
        Listing8OwnerTemplateCollection.Intact mode template reached.principal.memory ∧
        Listing8OwnerTemplateCollection.Decodes mode template reached.principal.memory := by
  rcases transitions_prefix mode start table valid state entry initial before after cut with ⟨packet,allowed,memory,kept⟩
  refine ⟨packet,allowed,memory,Listing8OriginalOwnerRegions.region_inside mode _ codeStart codeEnd
    (transitions_placed mode start table codeStart codeEnd placed) packet allowed,?_⟩
  intro template member outside
  have intact := kept template member outside
  exact ⟨intact,Listing8OwnerTemplateCollection.decodes mode template _ intact⟩

end SmcTuring.Appendix.Listing8DeclarationOwnerRegions

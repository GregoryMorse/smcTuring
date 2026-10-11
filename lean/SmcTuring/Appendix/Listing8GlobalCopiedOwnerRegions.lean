module
public import SmcTuring.Appendix.Listing8GlobalCopiedPointerRegions
public import SmcTuring.Appendix.Listing8GlobalMainBounds
public import SmcTuring.Appendix.Listing8MainOwnerWrites

public section
namespace SmcTuring.Appendix.Listing8GlobalCopiedOwnerRegions
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8OwnerSequence
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def Placement (mode : Mode) (origin : Nat) : Owner mode → Prop
  | .pointer source pc value => Listing8GlobalControlLayout.Allowed mode origin source (pointerSpan mode) ∧
      Listing8GlobalControlLayout.Allowed mode origin pc (pointerSpan mode) ∧
      Listing8GlobalControlLayout.Allowed mode origin value.toNat mode.wordBytes
  | .scalar _ target _ => Listing8GlobalControlLayout.Allowed mode origin target 4

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (owner : Owner mode) (member : owner∈Listing8OwnerImage.owners mode l (values mode origin g node rule))
    (observed : Nat × Nat) (inside : observed∈Listing8OwnerSequence.windows mode owner) :
    Listing8GlobalControlLayout.Allowed mode origin observed.1 observed.2 := by
  have block:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have originals:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  rcases Listing8CopiedOwners.window_bounds mode l _ owner member observed inside with code | sourceNode | sourceRule
  · right;left;constructor <;> omega
  · right;right;right;omega
  · right;right;right;omega

theorem graph_word (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) (word : Word mode)
    (member : word∈[(values mode origin g node rule).back,(values mode origin g node rule).forward,
      (values mode origin g node rule).next,(values mode origin g node rule).newState]) :
    Listing8GlobalControlLayout.Allowed mode origin word.toNat mode.wordBytes := by
  have owned : StringWrites.WordOwned mode (Listing8FullTableImage.start mode origin)
      (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) word := by
    simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Listing8LateGraphFieldBounds.node_word mode origin g (g.tape node).back bounds
    · exact Listing8LateGraphFieldBounds.node_word mode origin g (g.tape node).forward bounds
    · exact Listing8LateGraphFieldBounds.next_word mode origin g rule bounds
    · exact Listing8LateGraphFieldBounds.state_word mode origin g (g.rules rule).destination bounds
  exact Or.inr (Or.inr (Or.inr owned.1))

theorem advance_regions (mode : Mode) (origin : Nat) (owner : Owner mode) (placed : Placement mode origin owner)
    (state : StringExecution.State mode) (valid : Valid mode owner)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8OwnerSequence.pc mode owner))
    (current : Current mode owner state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((forms mode owner).map (StringStoreWrites.liftDword mode)) state := by
  cases owner with
  | pointer source pc value =>
    have mapping : (((Listing8CopiedPointer.forms mode source pc value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode))=
        (Listing8CopiedPointer.forms mode source pc value).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
    change StringStoreRegions.Run mode _
      (((Listing8CopiedPointer.forms mode source pc value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)) state
    rw [mapping]
    exact Listing8GlobalCopiedPointerRegions.regions mode origin source pc value state entry valid.1 valid.2.1
      placed.1 placed.2.1 placed.2.2 current.1 current.2
  | scalar pc target value =>
    exact BoundedStoreRegions.interval mode _ target (target+4) _ state
      (fun _ _ lower upper => Listing8GlobalStoreSubregions.within mode origin target 4 _ _ placed lower upper)
      ⟨StringStoreWrites.located mode target (target+4) pc target value state entry valid.2.2
        (by have bound:=valid.2.1;omega) ⟨Nat.le_refl _,Nat.le_refl _⟩,trivial⟩

theorem regions (mode : Mode) (origin : Nat) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (outside : ∀ writer∈owners,∀ reader∈owners,Outside mode writer reader)
    (placed : ∀ owner∈owners,Placement mode origin owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (current : Intact mode owners state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((program mode owners).map (StringStoreWrites.liftDword mode)) state := by
  induction owners generalizing start state with
  | nil => trivial
  | cons owner owners ih =>
    have v:=valid owner (List.Mem.head _)
    have c:=current owner (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode (Listing8OwnerSequence.pc mode owner) := by rw [chain.1];exact entry
    have first:=advance_regions mode origin owner (placed owner (List.Mem.head _)) state v location c
    have next:=advance_pc mode owner state v location c
    have kept : Intact mode owners (advance mode owner state).principal.memory := by
      intro reader member
      exact retained mode owner reader state v location c (current reader (List.Mem.tail _ member))
        (outside owner (List.Mem.head _) reader (List.Mem.tail _ member))
    have rest:=ih _ chain.2 (fun reader member => valid reader (List.Mem.tail _ member))
      (fun writer wm reader rm => outside writer (List.Mem.tail _ wm) reader (List.Mem.tail _ rm))
      (fun reader member => placed reader (List.Mem.tail _ member)) _ next kept
    rw [program,List.flatMap_cons,List.map_append,StringStoreRegions.append,Listing8OwnerSequenceWrites.advance_run mode owner state v location c]
    exact ⟨first,rest⟩

end SmcTuring.Appendix.Listing8GlobalCopiedOwnerRegions

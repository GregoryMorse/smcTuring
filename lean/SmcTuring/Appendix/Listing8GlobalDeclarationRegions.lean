module
public import SmcTuring.Appendix.Listing8LateGraphFieldBounds
public import SmcTuring.Appendix.Listing8GraphDeclarationWriteBounds
public import SmcTuring.Appendix.Listing8GlobalControlTemplates
public import SmcTuring.Native.BoundedStoreRegions

public section
namespace SmcTuring.Appendix.Listing8GlobalDeclarationRegions
open Native Listing8Prototypes Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext

theorem nodes (mode : Mode) (origin : Nat) (g : Graph) (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8DeclarationWrites.NodePlaced mode (Listing8FullTableImage.start mode origin) (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin g) := by
  apply Listing8GraphDeclarationWriteBounds.nodes_from_lookup
  intro index value found
  have within : index<g.nodes := by
    have small:=(List.getElem?_eq_some_iff.mp found).1;rw [Listing8GraphNodeImage.length] at small;exact small
  have actual:=Listing8GraphNodeImage.lookup mode origin g ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst value
  apply Listing8DeclarationWrites.node_fields
  · have lower:=(Listing8GraphLayout.transition_lower mode origin g.transitions).trans
      ((Listing8GraphLayout.table_before_input mode origin g.transitions).trans
        (Listing8GraphLayout.node_lower mode origin g.transitions index))
    have upper:=Listing8GraphLayout.node_upper mode origin g.transitions g.nodes index within
    exact ⟨lower,upper⟩
  · exact Listing8LateGraphFieldBounds.node_word mode origin g (g.tape ⟨index,within⟩).back bounds
  · exact Listing8LateGraphFieldBounds.node_word mode origin g (g.tape ⟨index,within⟩).forward bounds

theorem transitions (mode : Mode) (origin : Nat) (g : Graph) (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8DeclarationWrites.TransitionPlaced mode (Listing8FullTableImage.start mode origin) (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8FullTableImage.start mode origin) (table mode origin g) := by
  apply Listing8GraphDeclarationWriteBounds.transitions_from_lookup
  intro index value found
  have within : index<g.transitions := by
    have small:=(List.getElem?_eq_some_iff.mp found).1;rw [table_length] at small;exact small
  have actual:=lookup mode origin g ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst value
  apply Listing8DeclarationWrites.transition_fields
  · change Listing8FullTableImage.start mode origin≤Listing8GraphLayout.transition mode origin index ∧
      Listing8GraphLayout.transition mode origin index+transitionSpan mode≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes
    have lower:=Listing8GraphLayout.transition_lower mode origin index
    have upper:=Nat.le_trans (Listing8GraphLayout.transition_upper mode origin g.transitions index within)
      (Nat.le_trans (Listing8GraphLayout.table_before_input mode origin g.transitions) (Listing8LoopTailGeometry.input_before_end mode origin g))
    exact ⟨lower,upper⟩
  · exact Listing8LateGraphFieldBounds.next_word mode origin g ⟨index,within⟩ bounds
  · exact Listing8LateGraphFieldBounds.state_word mode origin g (g.rules ⟨index,within⟩).destination bounds


theorem node_regions (mode : Mode) (origin : Nat) (g : Graph) (bounds : Listing8GraphPointers.Bounds mode origin g)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8GraphLayout.input mode origin g.transitions))
    (current : Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin g) state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions)
        (Listing8GraphNodeImage.declarations mode origin g)).map (StringStoreWrites.liftDword mode)) state :=
  BoundedStoreRegions.interval mode _ _ _ _ state (fun _ _ lower _ => Or.inr (Or.inr (Or.inr lower)))
    (Listing8DeclarationWrites.nodes_owned mode _ _ _ _ (Listing8GraphNodeImage.valid mode origin g bounds)
      (nodes mode origin g bounds) state entry current)

theorem transition_regions (mode : Mode) (origin : Nat) (g : Graph) (bounds : Listing8GraphPointers.Bounds mode origin g)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin))
    (current : Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map (StringStoreWrites.liftDword mode)) state :=
  BoundedStoreRegions.interval mode _ _ _ _ state (fun _ _ lower _ => Or.inr (Or.inr (Or.inr lower)))
    (Listing8DeclarationWrites.transitions_owned mode _ _ _ _ (Listing8GraphTableBounds.declarations_valid mode origin g bounds)
      (transitions mode origin g bounds) state entry current)

end SmcTuring.Appendix.Listing8GlobalDeclarationRegions

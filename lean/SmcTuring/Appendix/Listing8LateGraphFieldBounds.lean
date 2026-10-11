module
public import SmcTuring.Appendix.Listing8GraphFieldWriteBounds

public section
namespace SmcTuring.Appendix.Listing8LateGraphFieldBounds
open Native Listing8SourceGraph

theorem node_word (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    StringWrites.WordOwned mode (Listing8FullTableImage.start mode origin) (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Arithmetic.encodeNat mode (nodePC mode origin g index)) := by
  have old:=Listing8GraphFieldWriteBounds.node_word mode origin g index bounds
  unfold StringWrites.WordOwned at old ⊢
  rw [Listing8GraphPointers.node_toNat mode origin g index bounds] at old ⊢
  exact ⟨(Listing8GraphLayout.transition_lower mode origin g.transitions).trans
    ((Listing8GraphLayout.table_before_input mode origin g.transitions).trans
      (Listing8GraphLayout.node_lower mode origin g.transitions index.val)),old.2⟩

theorem rule_word (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    StringWrites.WordOwned mode (Listing8FullTableImage.start mode origin) (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Arithmetic.encodeNat mode (rulePC mode origin g index)) := by
  have old:=Listing8GraphFieldWriteBounds.rule_word mode origin g index bounds
  unfold StringWrites.WordOwned at old ⊢
  rw [Listing8GraphPointers.rule_toNat mode origin g index bounds] at old ⊢
  exact ⟨Listing8GraphLayout.transition_lower mode origin index.val,old.2⟩

theorem state_word (mode : Mode) (origin : Nat) (g : Graph) (target : Option (Fin g.transitions))
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    StringWrites.WordOwned mode (Listing8FullTableImage.start mode origin) (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Arithmetic.encodeNat mode (statePC mode origin g target)) := by
  cases target with
  | none => exact node_word mode origin g g.halt bounds
  | some index => exact rule_word mode origin g index bounds

theorem next_word (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    StringWrites.WordOwned mode (Listing8FullTableImage.start mode origin) (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Arithmetic.encodeNat mode (nextPC mode origin g index)) := by
  unfold nextPC
  split_ifs with scan
  · exact rule_word mode origin g ⟨index.val+1,scan.2⟩ bounds
  · exact node_word mode origin g g.halt bounds

end SmcTuring.Appendix.Listing8LateGraphFieldBounds

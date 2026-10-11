module
public import SmcTuring.Appendix.Listing8DeclarationWrites
public import SmcTuring.Appendix.Listing8GraphFieldWriteBounds
public import SmcTuring.Appendix.Listing8ResetWrites

public section
namespace SmcTuring.Appendix.Listing8GraphDeclarationWriteBounds
open Native Listing8Prototypes Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext

theorem nodes_from_lookup (mode : Mode) (codeStart codeEnd pc : Nat) (items : List (Listing8NodeBlock.Values mode))
    (each : ∀ index value,items[index]?=some value →
      ∀ owner∈Listing8NodeBlock.owners mode (Listing8NodeTable.entryPC mode pc index) value,
        Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner) :
    Listing8DeclarationWrites.NodePlaced mode codeStart codeEnd pc items := by
  induction items generalizing pc with
  | nil => trivial
  | cons v items ih =>
    refine ⟨?_,?_⟩
    · simpa only [Listing8NodeTable.entryPC,Nat.zero_mul,Nat.add_zero] using each 0 v rfl
    · apply ih (pc+nodeSpan mode)
      intro index value found
      have actual:=each (index+1) value (by simpa only [List.getElem?_cons_succ] using found)
      have address : Listing8NodeTable.entryPC mode pc (index+1)=Listing8NodeTable.entryPC mode (pc+nodeSpan mode) index := by
        dsimp [Listing8NodeTable.entryPC];rw [Nat.add_mul,Nat.one_mul];omega
      rw [address] at actual;exact actual

theorem transitions_from_lookup (mode : Mode) (codeStart codeEnd pc : Nat) (items : List (Values mode))
    (each : ∀ index value,items[index]?=some value →
      ∀ owner∈Listing8TransitionBlock.owners mode (Listing8TransitionTable.entryPC mode pc index) value,
        Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner) :
    Listing8DeclarationWrites.TransitionPlaced mode codeStart codeEnd pc items := by
  induction items generalizing pc with
  | nil => trivial
  | cons v items ih =>
    refine ⟨?_,?_⟩
    · simpa only [Listing8TransitionTable.entryPC,Nat.zero_mul,Nat.add_zero] using each 0 v rfl
    · apply ih (pc+transitionSpan mode)
      intro index value found
      have actual:=each (index+1) value (by simpa only [List.getElem?_cons_succ] using found)
      have address : Listing8TransitionTable.entryPC mode pc (index+1)=Listing8TransitionTable.entryPC mode (pc+transitionSpan mode) index := by
        dsimp [Listing8TransitionTable.entryPC];rw [Nat.add_mul,Nat.one_mul];omega
      rw [address] at actual;exact actual

theorem nodes (mode : Mode) (origin : Nat) (g : Graph) (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8DeclarationWrites.NodePlaced mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8GraphLayout.input mode origin g.transitions) (Listing8GraphNodeImage.declarations mode origin g) := by
  apply nodes_from_lookup
  intro index value found
  have within : index<g.nodes := by
    have small:=(List.getElem?_eq_some_iff.mp found).1;rw [Listing8GraphNodeImage.length] at small;exact small
  have actual:=Listing8GraphNodeImage.lookup mode origin g ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst value
  apply Listing8DeclarationWrites.node_fields
  · have lower:=Nat.le_trans (Listing9EarlyImage.input_after_origin mode origin g.transitions)
      (Listing8GraphLayout.node_lower mode origin g.transitions index)
    have upper:=Listing8GraphLayout.node_upper mode origin g.transitions g.nodes index within
    exact ⟨lower,upper⟩
  · exact Listing8GraphFieldWriteBounds.node_word mode origin g (g.tape ⟨index,within⟩).back bounds
  · exact Listing8GraphFieldWriteBounds.node_word mode origin g (g.tape ⟨index,within⟩).forward bounds

theorem transitions (mode : Mode) (origin : Nat) (g : Graph) (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8DeclarationWrites.TransitionPlaced mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8FullTableImage.start mode origin) (table mode origin g) := by
  apply transitions_from_lookup
  intro index value found
  have within : index<g.transitions := by
    have small:=(List.getElem?_eq_some_iff.mp found).1;rw [table_length] at small;exact small
  have actual:=lookup mode origin g ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst value
  apply Listing8DeclarationWrites.transition_fields
  · change origin≤Listing8GraphLayout.transition mode origin index ∧
      Listing8GraphLayout.transition mode origin index+transitionSpan mode≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes
    have lower:=Listing8GraphLayout.transition_lower mode origin index
    have upper:=Nat.le_trans (Listing8GraphLayout.transition_upper mode origin g.transitions index within)
      (Nat.le_trans (Listing8GraphLayout.table_before_input mode origin g.transitions) (Listing8LoopTailGeometry.input_before_end mode origin g))
    constructor
    · rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset] at lower
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at lower ⊢ <;> omega
    · exact upper
  · exact Listing8GraphFieldWriteBounds.next_word mode origin g ⟨index,within⟩ bounds
  · exact Listing8GraphFieldWriteBounds.state_word mode origin g (g.rules ⟨index,within⟩).destination bounds

end SmcTuring.Appendix.Listing8GraphDeclarationWriteBounds

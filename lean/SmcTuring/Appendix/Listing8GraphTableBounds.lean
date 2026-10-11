module
public import SmcTuring.Appendix.Listing8GraphPointers
public import SmcTuring.Appendix.Listing8GraphReset

public section
namespace SmcTuring.Appendix.Listing8GraphTableBounds
open Native Listing8Prototypes Listing8SourceGraph

theorem valid_from_lookup (mode : Mode) (start : Nat) (declarations : List (Listing8CopyImage.Values mode))
    (each : ∀ index value,declarations[index]?=some value →
      Listing8TransitionBlock.Bounds mode (Listing8TransitionTable.entryPC mode start index) value) :
    Listing8TransitionTable.Valid mode start declarations := by
  induction declarations generalizing start with
  | nil => trivial
  | cons value declarations ih =>
    refine ⟨?_,?_⟩
    · simpa only [Listing8TransitionTable.entryPC,Nat.zero_mul,Nat.add_zero] using each 0 value rfl
    · apply ih (start+transitionSpan mode)
      intro index item lookup
      have current:=each (index+1) item (by simpa only [List.getElem?_cons_succ] using lookup)
      have address : Listing8TransitionTable.entryPC mode start (index+1)=
          Listing8TransitionTable.entryPC mode (start+transitionSpan mode) index := by
        dsimp [Listing8TransitionTable.entryPC]
        rw [Nat.add_mul,Nat.one_mul]
        omega
      rw [address] at current
      exact current

theorem declarations_valid (mode : Mode) (origin : Nat) (g : Graph)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8TransitionTable.Valid mode (Listing8FullTableImage.start mode origin) (table mode origin g) := by
  apply valid_from_lookup
  intro index value found
  have within : index<g.transitions := by
    have small:=List.getElem?_eq_some_iff.mp found |>.1
    rw [table_length] at small
    exact small
  have actual:=lookup mode origin g ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst value
  exact Listing8GraphPointers.transition_bounds mode origin g g.halt ⟨index,within⟩ bounds

theorem table_bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes)
    (l : Listing8CopyImage.Layout) (located : l.sourceNode=nodePC mode origin g node)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8FullTableImage.Bounds mode origin l (table mode origin g) := by
  have after:=Listing8GraphLayout.table_before_input mode origin g.transitions
  have lower:=Listing8GraphLayout.node_lower mode origin g.transitions node.val
  have cap:=Listing8GraphReset.capacity mode origin g.transitions g.nodes bounds
  rw [Listing8GraphReset.endpoint] at cap
  refine ⟨declarations_valid mode origin g bounds,?_,?_⟩
  · simp only [Listing8TransitionTable.endPC,table_length]
    change Listing8GraphLayout.reset mode origin g.transitions<_
    omega
  · rw [located]
    simp only [Listing8TransitionTable.endPC,table_length]
    exact Nat.le_trans after lower

theorem reset_bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes)
    (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets) (sentinel : Nat)
    (located : l.sourceNode=nodePC mode origin g node)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8TableResetImage.Bounds mode origin l sentinel (table mode origin g) := by
  refine ⟨table_bounds mode origin g node l located bounds,?_,?_⟩
  · apply Listing8GraphReset.actual_valid mode origin l t sentinel g.nodes (table mode origin g) boot body
    simpa only [table_length] using bounds
  · rw [Listing8GraphReset.actual_region mode origin l t sentinel (table mode origin g) boot body,
      Listing8GraphReset.endpoint,table_length,located]
    exact Listing8GraphLayout.node_lower mode origin g.transitions node.val

end SmcTuring.Appendix.Listing8GraphTableBounds

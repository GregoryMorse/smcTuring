module
public import SmcTuring.Appendix.Listing8GraphPointers

public section
namespace SmcTuring.Appendix.Listing8GraphOwnerBounds
open Native Listing8Prototypes Listing8SourceGraph Listing8CopyImage
/-- Remaining fixed body-field conditions. Graph-word capacity and ownership
are derived separately from the constructed finite graph. -/
structure Fields (mode : Mode) (l : Layout) : Prop where
  directionAfter : Listing8LiteralInput.endPC mode l.input≤l.direction
  directionFits : l.direction+10<2^(8*mode.wordBytes)
  nodeDirection : l.sourceNode+nodeSpan mode≤l.direction+6 ∨ l.direction+10≤l.sourceNode
  transitionDirection : l.sourceTransition+transitionSpan mode≤l.direction+6 ∨ l.direction+10≤l.sourceTransition
  tapeReach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input)
  ruleReach : mode=.x64 → Relocation.SignedDelta (currentEntry mode (transitionParams mode l).destination+10) (Listing8LiteralInput.scalarField mode l.input)
  freshReach : mode=.x64 → Relocation.SignedDelta (newEntry mode (transitionParams mode l).destination+10) (Listing8LiteralInput.updateStart mode l.input+6)
  directionReach : mode=.x64 → Relocation.SignedDelta (directionEntry mode (transitionParams mode l).destination+10) (l.direction+6)

theorem code_before_table (mode : Mode) (origin : Nat) (l : Layout)
    (packed : l.start=Listing4EntryLayout.mainPC mode origin) :
    codeEnd mode l≤Listing8FullTableImage.start mode origin := by
  rw [(Listing8Initializer.code_geometry mode l).2.2,packed,Listing8FullTableImage.start,Listing8FailLayout.end_offset]
  cases mode <;> dsimp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size] <;> omega
theorem node_after_table (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes) :
    Listing8FullTableImage.start mode origin≤nodePC mode origin g index :=
  Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions)
    (Nat.le_trans (Listing8GraphLayout.table_before_input mode origin g.transitions)
      (Listing8GraphLayout.node_lower mode origin g.transitions index.val))
theorem state_after_table (mode : Mode) (origin : Nat) (g : Graph) (target : Option (Fin g.transitions)) :
    Listing8FullTableImage.start mode origin≤statePC mode origin g target := by
  cases target with
  | none => exact node_after_table mode origin g g.halt
  | some index => exact Listing8GraphLayout.transition_lower mode origin index.val
theorem next_after_table (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.transitions) :
    Listing8FullTableImage.start mode origin≤nextPC mode origin g index := by
  unfold nextPC
  split_ifs
  · exact Listing8GraphLayout.transition_lower mode origin (index.val+1)
  · exact node_after_table mode origin g g.halt

theorem graph (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (packed : l.start=Listing4EntryLayout.mainPC mode origin) (bounds : Listing8GraphPointers.Bounds mode origin g) :
    ∀ word∈[(values mode origin g node rule).back,(values mode origin g node rule).forward,
      (values mode origin g node rule).next,(values mode origin g node rule).newState],
      (word.toNat+mode.wordBytes≤l.start ∨ codeEnd mode l≤word.toNat) ∧ word.toNat+mode.wordBytes<2^(8*mode.wordBytes) := by
  have before:=code_before_table mode origin l packed
  intro word member
  simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [Listing8GraphPointers.node_toNat mode origin g (g.tape node).back bounds]
    exact ⟨Or.inr (Nat.le_trans before (node_after_table mode origin g _)),Listing8GraphPointers.node_capacity mode origin g _ bounds⟩
  · rw [Listing8GraphPointers.node_toNat mode origin g (g.tape node).forward bounds]
    exact ⟨Or.inr (Nat.le_trans before (node_after_table mode origin g _)),Listing8GraphPointers.node_capacity mode origin g _ bounds⟩
  · rw [Listing8GraphPointers.next_toNat mode origin g rule bounds]
    exact ⟨Or.inr (Nat.le_trans before (next_after_table mode origin g rule)),Listing8GraphPointers.next_capacity mode origin g rule bounds⟩
  · rw [Listing8GraphPointers.state_toNat mode origin g (g.rules rule).destination bounds]
    exact ⟨Or.inr (Nat.le_trans before (state_after_table mode origin g _)),Listing8GraphPointers.state_capacity mode origin g _ bounds⟩
theorem bounds (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (packed : l.start=Listing4EntryLayout.mainPC mode origin) (fields : Fields mode l)
    (native : Listing8GraphPointers.Bounds mode origin g) :
    Listing8CopiedOwners.Bounds mode l (values mode origin g node rule) :=
  ⟨graph mode origin l g node rule packed native,fields.directionAfter,fields.directionFits,
    fields.nodeDirection,fields.transitionDirection,fields.tapeReach,fields.ruleReach,fields.freshReach,fields.directionReach⟩
end SmcTuring.Appendix.Listing8GraphOwnerBounds

module
public import SmcTuring.Appendix.Listing8GraphFieldWriteBounds
public import SmcTuring.Appendix.Listing8OwnerSequenceWrites

public section
namespace SmcTuring.Appendix.Listing8GraphCopiedWriteBounds
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev Owner:=Listing8OwnerSequence.Owner

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (owner : Owner mode) (member : owner∈Listing8OwnerImage.owners mode l (values mode origin g node rule))
    (observed : Nat × Nat) (windowMember : observed∈Listing8OwnerSequence.windows mode owner) :
    origin≤observed.1 ∧ observed.1+observed.2≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  have placed:=Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx
  rcases Listing8CopiedOwners.window_bounds mode l _ owner member observed windowMember with code | sourceNode | sourceRule
  · have bounds:=placed.block;exact ⟨by omega,by omega⟩
  · have bounds:=placed.node;exact ⟨by omega,by omega⟩
  · have bounds:=placed.transition;exact ⟨by omega,by omega⟩

theorem pointer (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (source pc : Nat) (value : Word mode)
    (member : (.pointer source pc value : Owner mode)∈Listing8OwnerImage.owners mode l (values mode origin g node rule))
    (valueMember : value∈[(values mode origin g node rule).back,(values mode origin g node rule).forward,
      (values mode origin g node rule).next,(values mode origin g node rule).newState]) :
    Listing8OwnerSequenceWrites.Placement mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) (.pointer source pc value) := by
  have original:=window mode origin l t g node rule ctx _ member (source,(pointerBytes mode source value).length) (by simp [Listing8OwnerSequence.windows])
  have copied:=window mode origin l t g node rule ctx _ member (pc,(pointerBytes mode source value).length) (by simp [Listing8OwnerSequence.windows])
  rw [pointer_length] at original copied
  exact ⟨original,copied,Listing8GraphFieldWriteBounds.graph_words mode origin g node rule ctx.native value valueMember⟩

/-- All seven actual copied owner placements follow from original windows,
logical graph words and the literal input/direction field geometry. -/
theorem placement (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    ∀ owner∈Listing8OwnerImage.owners mode l (values mode origin g node rule),
      Listing8OwnerSequenceWrites.Placement mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) owner := by
  have input:=Listing8GraphFieldWriteBounds.input mode origin l t g node rule ctx
  have direction:=Listing8GraphFieldWriteBounds.direction mode origin l t g node rule ctx
  have scalars:=Listing8CopiedOwners.scalar_bounds mode l
  intro owner member
  simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointer mode origin l t g node rule ctx _ _ _ (by simp [Listing8OwnerImage.owners]) (by simp)
  · exact pointer mode origin l t g node rule ctx _ _ _ (by simp [Listing8OwnerImage.owners]) (by simp)
  · exact pointer mode origin l t g node rule ctx _ _ _ (by simp [Listing8OwnerImage.owners]) (by simp)
  · exact ⟨by omega,by omega⟩
  · exact ⟨by omega,by omega⟩
  · exact ⟨by omega,by omega⟩
  · exact pointer mode origin l t g node rule ctx _ _ _ (by simp [Listing8OwnerImage.owners]) (by simp)

end SmcTuring.Appendix.Listing8GraphCopiedWriteBounds

module
public import SmcTuring.Native.StringReadRuns
public import SmcTuring.Native.StringMoves

public section
namespace SmcTuring.Native.StringMoveReads

/-- The distinct SI read window is bounded at every actual forward MOVS
state, with nonwrapping cursor advances derived from the original total. -/
theorem contained (mode : Mode) (start stop : Nat) (widths : List Nat) (state : StringExecution.State mode)
    (forward : state.backwards=false)
    (fits : state.sourceIndex.toNat+widths.sum<2^(8*mode.wordBytes))
    (inside : start≤state.sourceIndex.toNat ∧ state.sourceIndex.toNat+widths.sum≤stop) :
    StringReadRuns.Run mode ⟨start,stop⟩ ((StringMoves.forms mode widths).map (StringWrites.liftString mode)) state := by
  induction widths generalizing state with
  | nil => trivial
  | cons width rest ih =>
    have headFits : state.sourceIndex.toNat+width<2^(8*mode.wordBytes) := by simp only [List.sum_cons] at fits;omega
    have next : (StringExecution.execute mode (.move width) state).sourceIndex.toNat=state.sourceIndex.toNat+width := by
      rw [StringExecution.move_effect mode width state forward]
      exact StringMoves.index_advance mode _ _ headFits
    have nextFits : (StringExecution.execute mode (.move width) state).sourceIndex.toNat+rest.sum<2^(8*mode.wordBytes) := by
      rw [next];simp only [List.sum_cons] at fits;omega
    have nextInside : start≤(StringExecution.execute mode (.move width) state).sourceIndex.toNat ∧
        (StringExecution.execute mode (.move width) state).sourceIndex.toNat+rest.sum≤stop := by
      rw [next];simp only [List.sum_cons] at inside;constructor <;> omega
    constructor
    · change start≤state.sourceIndex.toNat ∧ state.sourceIndex.toNat+width≤stop
      exact ⟨inside.1,by simp only [List.sum_cons] at inside;omega⟩
    · exact ih _ ((StringExecution.direction_preserved mode _ state).trans forward) nextFits nextInside

end SmcTuring.Native.StringMoveReads

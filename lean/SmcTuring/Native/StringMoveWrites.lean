module
public import SmcTuring.Native.StringWrites
public import SmcTuring.Native.StringMoves

public section
namespace SmcTuring.Native.StringMoveWrites

/-- A forward MOVS really writes every byte of its complete positive-width
element. Its range is a code range, independently of the copied values. -/
theorem move (mode : Mode) (codeStart codeEnd width : Nat) (state : StringExecution.State mode)
    (positive : 0<width) (inside : codeStart≤state.destinationIndex.toNat ∧ state.destinationIndex.toNat+width≤codeEnd) :
    StringWrites.CodeWrite mode codeStart codeEnd (StringWrites.liftString mode (.move width)) state := by
  unfold StringWrites.CodeWrite
  simpa only [StringWrites.packet,StringWrites.control,StringWrites.dword,StringWrites.string,StringWrites.liftString,ByteMemory.bytes_at_length] using
    (show 0<width ∧ codeStart≤state.destinationIndex.toNat ∧ state.destinationIndex.toNat+width≤codeEnd from ⟨positive,inside⟩)

theorem owned (mode : Mode) (codeStart codeEnd : Nat) (widths : List Nat) (state : StringExecution.State mode)
    (positive : ∀ width∈widths,0<width) (forward : state.backwards=false)
    (fits : state.destinationIndex.toNat+widths.sum<2^(8*mode.wordBytes))
    (inside : codeStart≤state.destinationIndex.toNat ∧ state.destinationIndex.toNat+widths.sum≤codeEnd) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringMoves.forms mode widths).map (StringWrites.liftString mode)) state := by
  induction widths generalizing state with
  | nil => trivial
  | cons width rest ih =>
    have headFits : state.destinationIndex.toNat+width<2^(8*mode.wordBytes) := by simp only [List.sum_cons] at fits;omega
    have next : (StringExecution.execute mode (.move width) state).destinationIndex.toNat=state.destinationIndex.toNat+width := by
      rw [StringExecution.move_effect mode width state forward]
      exact StringMoves.index_advance mode _ _ headFits
    have nextFits : (StringExecution.execute mode (.move width) state).destinationIndex.toNat+rest.sum<2^(8*mode.wordBytes) := by
      rw [next];simp only [List.sum_cons] at fits;omega
    have nextInside : codeStart≤(StringExecution.execute mode (.move width) state).destinationIndex.toNat ∧
        (StringExecution.execute mode (.move width) state).destinationIndex.toNat+rest.sum≤codeEnd := by
      rw [next];simp only [List.sum_cons] at inside;constructor <;> omega
    exact ⟨move mode codeStart codeEnd width state (positive width (by simp)) (by simp only [List.sum_cons] at inside;exact ⟨inside.1,by omega⟩),
      ih (StringExecution.execute mode (.move width) state) (fun item member => positive item (by simp [member]))
        ((StringExecution.direction_preserved mode _ state).trans forward) nextFits nextInside⟩

end SmcTuring.Native.StringMoveWrites

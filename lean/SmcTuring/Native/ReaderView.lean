module
public import SmcTuring.Native.Fragment

public section

namespace SmcTuring.Native.ReaderView

open Execution ControlImage ReaderImage

theorem label_owned (mode : Mode) (start origin : Nat) (initial : Word mode) (whole : List (SpacedPacking.Piece mode))
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start initial))
      (SpacedPacking.place mode origin whole)) :
    Owned mode (SpacedPacking.place mode origin whole) (label mode start) :=
  Fragment.owned_view mode _ _ _ within (ReaderImage.label_owned mode start initial fits)

/-- The placed reader works within the complete constructed image. Its loaded
pointer may name its own label, another reader, scalar metadata, or grid data.
The actual ownership and separation proofs establish final-packet safety. -/
theorem trace (mode : Mode) (start origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : origin + SpacedPacking.size mode whole <= gridBase - moffsOperandOffset mode)
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start initial))
      (SpacedPacking.place mode origin whole))
    (intact : SpacedCombinedImage.Intact mode whole origin gridBase state.memory)
    (pointerOwned : SpacedCombinedImage.Owned mode whole origin gridBase (load mode state.memory (label mode start))) :
    Fetch.Trace mode state
      [.memory .exchangeAcc (firstDisp mode start), Reader.storeForm mode (label mode start) (secondDisp mode),
        .exchangeIndirect, .moffs (load mode state.memory (label mode start))]
      (Reader.finish mode state (label mode start) (firstDisp mode start) (secondDisp mode)) := by
  have firstMember : List.Mem (firstEntry mode start) (ControlPacking.place mode start (packets mode start initial)) := by
    rw [placed_roles]; exact List.Mem.head _
  have secondMember : List.Mem (secondEntry mode start) (ControlPacking.place mode start (packets mode start initial)) := by
    rw [placed_roles]; exact List.Mem.tail _ (List.Mem.head _)
  have thirdMember : List.Mem (thirdEntry mode start) (ControlPacking.place mode start (packets mode start initial)) := by
    rw [placed_roles]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have lastMember : List.Mem (lastEntry mode start initial) (ControlPacking.place mode start (packets mode start initial)) := by
    rw [placed_roles]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have positions := reached_positions mode start state location fits
  have firstHits := first_hits mode start state location
  have secondHits := second_hits mode start state location
  have labelOwned : SpacedCombinedImage.Owned mode whole origin gridBase (label mode start) :=
    Or.inl (label_owned mode start origin initial whole fits within)
  have swappedIntact : SpacedCombinedImage.Intact mode whole origin gridBase
      (Reader.swapped mode state (firstDisp mode start)).memory := by
    apply SpacedCombinedImage.execute_intact mode whole origin gridBase state (.memory .exchangeAcc (firstDisp mode start)) enough gap intact
    change SpacedCombinedImage.Owned mode whole origin gridBase
      (memoryAddress mode (nextPC mode (.memory .exchangeAcc (firstDisp mode start)) state) (firstDisp mode start))
    rw [firstHits]; exact labelOwned
  have current := Protected.current_moffs mode state.memory (start + prefixSize mode)
    (intact.1 _ (within _ lastMember))
  have word : Protected.wordAt mode state.memory (start + prefixSize mode + moffsOperandOffset mode) =
      load mode state.memory (label mode start) := by
    unfold load Protected.wordAt
    rw [label_location mode start initial fits]
    rfl
  rw [word] at current
  have safe := Fragment.owned_packet_safe mode whole origin gridBase (lastEntry mode start initial)
    (within _ lastMember) (label mode start) (load mode state.memory (label mode start))
    (label_location mode start initial fits) gap pointerOwned
  apply Reader.trace_of_fetches
  · rw [positions.1]
    exact fetch_current mode (firstEntry mode start) state.memory (intact.1 _ (within _ firstMember))
  · rw [positions.2.1]
    exact fetch_current mode (secondEntry mode start) _ (swappedIntact.1 _ (within _ secondMember))
  · rw [Reader.restored_memory mode state _ _ _ firstHits secondHits, positions.2.2.1]
    exact fetch_current mode (thirdEntry mode start) state.memory (intact.1 _ (within _ thirdMember))
  · apply Reader.fetch_last mode state _ _ _ firstHits secondHits
    · rw [positions.2.2.2]; exact current
    · rcases safe with same | separate
      · exact Or.inl same
      · apply Or.inr
        intro index
        let observed : Fin ((lastEntry mode start initial).bytes mode).length :=
          ⟨index.val, by simpa [lastEntry, Entry.bytes, Packet.bytes, instructionLength] using index.isLt⟩
        simpa only [positions.2.2.2, lastEntry] using separate observed

theorem owned_run (mode : Mode) (start origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (fits : start + totalSize mode < 2 ^ (8 * mode.wordBytes))
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start initial))
      (SpacedPacking.place mode origin whole))
    (pointerOwned : SpacedCombinedImage.Owned mode whole origin gridBase (load mode state.memory (label mode start))) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode whole origin gridBase)
      [.memory .exchangeAcc (firstDisp mode start), Reader.storeForm mode (label mode start) (secondDisp mode),
        .exchangeIndirect, .moffs (load mode state.memory (label mode start))] state := by
  have fields := Reader.four_writes_owned mode state (label mode start) (firstDisp mode start) (secondDisp mode)
    (first_hits mode start state location) (second_hits mode start state location)
    (SpacedCombinedImage.Owned mode whole origin gridBase)
    (Or.inl (label_owned mode start origin initial whole fits within)) pointerOwned
  simpa only [Writes.OwnedRun, and_true, Reader.swapped, Reader.restored, Reader.dereferenced] using fields

end SmcTuring.Native.ReaderView

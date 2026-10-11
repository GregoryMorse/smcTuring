module
public import SmcTuring.Native.StringTemplate
public import SmcTuring.Native.StringMoveWrites

public section
namespace SmcTuring.Native.StringCopyPrefixes

/-- The copied snapshot may come from a distinct initial memory. Cursor-save
overlays in the backing memory cannot alter bytes supplied by that snapshot. -/
theorem snapshot_window (backing initial : ByteMemory.Memory) (source destination size offset count : Nat)
    (complete : offset+count≤size) :
    ByteMemory.bytesAt (ByteMemory.putBytes backing destination (ByteMemory.bytesAt initial source size))
      (destination+offset) count=ByteMemory.bytesAt initial (source+offset) count := by
  apply congrArg List.ofFn
  funext index
  have small := index.isLt
  have bound : offset+index.val<(ByteMemory.bytesAt initial source size).length := by
    rw [ByteMemory.bytes_at_length];omega
  have written := ByteMemory.put_at_index backing destination (ByteMemory.bytesAt initial source size) ⟨offset+index.val,bound⟩
  simpa only [ByteMemory.bytesAt,List.getElem_ofFn,Nat.add_assoc] using written

theorem apart_prefix (source destination : Nat) (before after : List Nat)
    (apart : StringCopy.Apart source destination (before++after).sum) :
    StringCopy.Apart source destination before.sum := by
  unfold StringCopy.Apart at *
  rw [List.sum_append] at apart
  rcases apart with left | right
  · left;omega
  · right;omega

/-- Every actual MOVS prefix equals the exact prefix of the initial snapshot,
with a contiguous destination interval of the exact completed byte count. -/
theorem memory (mode : Mode) (before after : List Nat) (state : StringExecution.State mode)
    (forward : state.backwards=false)
    (sourceFits : state.sourceIndex.toNat+(before++after).sum<2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+(before++after).sum<2^(8*mode.wordBytes))
    (apart : StringCopy.Apart state.sourceIndex.toNat state.destinationIndex.toNat (before++after).sum) :
    (StringWrites.run mode ((StringMoves.forms mode before).map (StringWrites.liftString mode)) state).principal.memory=
      ByteMemory.putBytes state.principal.memory state.destinationIndex.toNat
        (ByteMemory.bytesAt state.principal.memory state.sourceIndex.toNat before.sum) := by
  rw [StringWrites.run_lift_string]
  apply StringMoves.effect mode before state forward
  · rw [List.sum_append] at sourceFits;omega
  · rw [List.sum_append] at destinationFits;omega
  · exact apart_prefix _ _ before after apart

theorem indices (mode : Mode) (before after : List Nat) (state : StringExecution.State mode)
    (forward : state.backwards=false)
    (sourceFits : state.sourceIndex.toNat+(before++after).sum<2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+(before++after).sum<2^(8*mode.wordBytes)) :
    let reached := StringWrites.run mode ((StringMoves.forms mode before).map (StringWrites.liftString mode)) state
    reached.sourceIndex.toNat=state.sourceIndex.toNat+before.sum ∧
    reached.destinationIndex.toNat=state.destinationIndex.toNat+before.sum ∧ reached.backwards=false := by
  rw [StringWrites.run_lift_string]
  refine ⟨?_,?_,?_⟩
  · rw [StringMoves.run_source mode before state forward]
    exact StringMoves.index_advance mode _ _ (by rw [List.sum_append] at sourceFits;omega)
  · rw [StringMoves.run_destination mode before state forward]
    exact StringMoves.index_advance mode _ _ (by rw [List.sum_append] at destinationFits;omega)
  · exact (StringExecution.run_direction mode _ state).trans forward

theorem copied_window (mode : Mode) (before after : List Nat) (state : StringExecution.State mode)
    (forward : state.backwards=false)
    (sourceFits : state.sourceIndex.toNat+(before++after).sum<2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+(before++after).sum<2^(8*mode.wordBytes))
    (apart : StringCopy.Apart state.sourceIndex.toNat state.destinationIndex.toNat (before++after).sum)
    (offset count : Nat) (complete : offset+count≤before.sum) :
    ByteMemory.bytesAt (StringWrites.run mode ((StringMoves.forms mode before).map (StringWrites.liftString mode)) state).principal.memory
      (state.destinationIndex.toNat+offset) count=
      ByteMemory.bytesAt state.principal.memory (state.sourceIndex.toNat+offset) count := by
  rw [memory mode before after state forward sourceFits destinationFits apart]
  exact StringTemplate.copied_window _ _ _ _ _ _ complete

theorem source_window (mode : Mode) (before after : List Nat) (state : StringExecution.State mode)
    (forward : state.backwards=false)
    (sourceFits : state.sourceIndex.toNat+(before++after).sum<2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+(before++after).sum<2^(8*mode.wordBytes))
    (apart : StringCopy.Apart state.sourceIndex.toNat state.destinationIndex.toNat (before++after).sum)
    (offset count : Nat) (within : offset+count≤(before++after).sum) :
    ByteMemory.bytesAt (StringWrites.run mode ((StringMoves.forms mode before).map (StringWrites.liftString mode)) state).principal.memory
      (state.sourceIndex.toNat+offset) count=
      ByteMemory.bytesAt state.principal.memory (state.sourceIndex.toNat+offset) count := by
  rw [memory mode before after state forward sourceFits destinationFits apart]
  apply ByteMemory.bytes_at_frame
  intro index inside
  have small := index.isLt
  simp only [ByteMemory.bytes_at_length,ByteMemory.Inside] at inside
  unfold StringCopy.Apart at apart
  rw [List.sum_append] at apart within
  rcases apart with left | right <;> omega

/-- The next actual packet reads the initial snapshot at its computed prefix
offset, rather than a supplied later value or read window. -/
theorem next_packet (mode : Mode) (before after : List Nat) (width : Nat) (state : StringExecution.State mode)
    (forward : state.backwards=false)
    (sourceFits : state.sourceIndex.toNat+(before++width::after).sum<2^(8*mode.wordBytes))
    (destinationFits : state.destinationIndex.toNat+(before++width::after).sum<2^(8*mode.wordBytes))
    (apart : StringCopy.Apart state.sourceIndex.toNat state.destinationIndex.toNat (before++width::after).sum) :
    let reached := StringWrites.run mode ((StringMoves.forms mode before).map (StringWrites.liftString mode)) state
    StringWrites.packet mode (StringWrites.liftString mode (.move width)) reached=
      ⟨state.destinationIndex.toNat+before.sum,
        ByteMemory.bytesAt state.principal.memory (state.sourceIndex.toNat+before.sum) width⟩ := by
  have cursors := indices mode before (width::after) state forward sourceFits destinationFits
  change (⟨(StringWrites.run mode ((StringMoves.forms mode before).map (StringWrites.liftString mode)) state).destinationIndex.toNat,
    ByteMemory.bytesAt (StringWrites.run mode ((StringMoves.forms mode before).map (StringWrites.liftString mode)) state).principal.memory
      (StringWrites.run mode ((StringMoves.forms mode before).map (StringWrites.liftString mode)) state).sourceIndex.toNat width⟩ : StringWrites.Packet)=_
  rw [cursors.1,cursors.2.1,source_window mode before (width::after) state forward sourceFits destinationFits apart]
  simp only [List.sum_append,List.sum_cons];omega

/-- An arbitrary cut of the returned native instruction list is an actual
width-prefix cut. This does not assume a special caller-chosen decomposition. -/
theorem cut (mode : Mode) (widths : List Nat) (before after : List (StringStack.Form mode))
    (split : (StringMoves.forms mode widths).map (StringWrites.liftString mode)=before++after) :
    ∃ first rest : List Nat,widths=first++rest ∧
      before=(StringMoves.forms mode first).map (StringWrites.liftString mode) ∧
      after=(StringMoves.forms mode rest).map (StringWrites.liftString mode) := by
  simp only [StringMoves.forms,List.map_map] at split
  rcases List.map_eq_append_iff.mp split with ⟨first,rest,whole,left,right⟩
  refine ⟨first,rest,whole,?_,?_⟩
  · simpa only [StringMoves.forms,List.map_map] using left.symm
  · simpa only [StringMoves.forms,List.map_map] using right.symm

end SmcTuring.Native.StringCopyPrefixes

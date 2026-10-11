module
public import SmcTuring.Native.StringCopyPrefixes
public import SmcTuring.Native.StringMacroTrace

public section
namespace SmcTuring.Native.StringMacroCopyPrefixes
open StringMacroLayout StringMacroEffects

@[expose] def reached (mode : Mode) (p : Params) (state : StringExecution.State mode) (widths : List Nat) :=
  StringWrites.run mode ((StringMoves.forms mode widths).map (StringWrites.liftString mode)) (setup mode p state)

theorem geometry (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state) :
    (setup mode p state).backwards=false ∧ (setup mode p state).sourceIndex.toNat=p.source ∧
    (setup mode p state).destinationIndex.toNat=p.destination ∧ (StringPlan.widths mode p.size).sum=p.size := by
  refine ⟨?_,?_,?_,StringPlan.total mode p.size⟩
  · rw [setup_effect mode p state ready];exact ready.forward
  · rw [setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ (source_capacity mode p state ready).2.2]
  · rw [setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ (destination_capacity mode p state ready).2.2]

/-- Setup's actual cursor saves do not alter any initial source subwindow. -/
theorem source_window (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state)
    (offset count : Nat) (within : offset+count≤p.size) :
    ByteMemory.bytesAt (setup mode p state).principal.memory (p.source+offset) count=
      ByteMemory.bytesAt state.principal.memory (p.source+offset) count := by
  rw [setup_effect mode p state ready]
  unfold StringFields.prepared StringMacroLayout.layout ByteMemory.putWord
  have separate := fields_separate mode p state ready
  rw [ByteMemory.bytes_at_frame,ByteMemory.bytes_at_frame]
  · intro index
    have small := index.isLt
    let observed : Fin p.size := ⟨offset+index.val,by omega⟩
    simpa only [StringMacroLayout.layout,LittleEndian.word_encode_length,Nat.add_assoc] using separate.2.2.1 observed
  · intro index
    have small := index.isLt
    let observed : Fin p.size := ⟨offset+index.val,by omega⟩
    simpa only [StringMacroLayout.layout,LittleEndian.word_encode_length,Nat.add_assoc] using separate.2.2.2.1 observed

theorem prefix_bounds (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state)
    (first rest : List Nat) (split : StringPlan.widths mode p.size=first++rest) :
    (setup mode p state).sourceIndex.toNat+(first++rest).sum<2^(8*mode.wordBytes) ∧
    (setup mode p state).destinationIndex.toNat+(first++rest).sum<2^(8*mode.wordBytes) ∧
    StringCopy.Apart (setup mode p state).sourceIndex.toNat (setup mode p state).destinationIndex.toNat (first++rest).sum ∧
    first.sum+rest.sum=p.size := by
  have g := geometry mode p state ready
  have total : (first++rest).sum=p.size := by rw [←split];exact g.2.2.2
  rw [g.2.1,g.2.2.1,total]
  exact ⟨(source_capacity mode p state ready).1,(destination_capacity mode p state ready).1,ready.buffers,
    by simpa only [List.sum_append] using total⟩

theorem memory (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state)
    (first rest : List Nat) (split : StringPlan.widths mode p.size=first++rest) :
    (reached mode p state first).principal.memory=
      ByteMemory.putBytes (StringFields.prepared mode (layout mode p) state.principal.memory state.sourceIndex state.destinationIndex)
        p.destination (ByteMemory.bytesAt state.principal.memory p.source first.sum) := by
  have g := geometry mode p state ready
  have b := prefix_bounds mode p state ready first rest split
  rw [reached,StringCopyPrefixes.memory mode first rest (setup mode p state) g.1 b.1 b.2.1 b.2.2.1,g.2.1,g.2.2.1]
  have source := source_window mode p state ready 0 first.sum (by have total := b.2.2.2;omega)
  simp only [Nat.add_zero] at source
  rw [source]
  rw [setup_effect mode p state ready]

theorem indices (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state)
    (first rest : List Nat) (split : StringPlan.widths mode p.size=first++rest) :
    (reached mode p state first).sourceIndex.toNat=p.source+first.sum ∧
    (reached mode p state first).destinationIndex.toNat=p.destination+first.sum ∧
    (reached mode p state first).backwards=false := by
  have g := geometry mode p state ready
  have b := prefix_bounds mode p state ready first rest split
  simpa only [reached,g.2.1,g.2.2.1] using StringCopyPrefixes.indices mode first rest (setup mode p state) g.1 b.1 b.2.1

theorem copied_window (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state)
    (first rest : List Nat) (split : StringPlan.widths mode p.size=first++rest)
    (offset count : Nat) (complete : offset+count≤first.sum) :
    ByteMemory.bytesAt (reached mode p state first).principal.memory (p.destination+offset) count=
      ByteMemory.bytesAt state.principal.memory (p.source+offset) count := by
  rw [memory mode p state ready first rest split]
  exact StringCopyPrefixes.snapshot_window _ _ _ _ _ _ _ complete

theorem source_window_after (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state)
    (first rest : List Nat) (split : StringPlan.widths mode p.size=first++rest)
    (offset count : Nat) (within : offset+count≤p.size) :
    ByteMemory.bytesAt (reached mode p state first).principal.memory (p.source+offset) count=
      ByteMemory.bytesAt state.principal.memory (p.source+offset) count := by
  have g := geometry mode p state ready
  have b := prefix_bounds mode p state ready first rest split
  have kept := StringCopyPrefixes.source_window mode first rest (setup mode p state) g.1 b.1 b.2.1 b.2.2.1
    offset count (by rw [←split,g.2.2.2];exact within)
  rw [g.2.1] at kept
  exact kept.trans (source_window mode p state ready offset count within)

theorem next_packet (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state)
    (first rest : List Nat) (width : Nat) (split : StringPlan.widths mode p.size=first++width::rest) :
    StringWrites.packet mode (StringWrites.liftString mode (.move width)) (reached mode p state first)=
      ⟨p.destination+first.sum,ByteMemory.bytesAt state.principal.memory (p.source+first.sum) width⟩ := by
  have g := geometry mode p state ready
  have b := prefix_bounds mode p state ready first (width::rest) split
  rw [reached,StringCopyPrefixes.next_packet mode first rest width (setup mode p state) g.1 b.1 b.2.1 b.2.2.1,g.2.1,g.2.2.1]
  rw [source_window mode p state ready first.sum width]
  have total := b.2.2.2
  simp only [List.sum_cons] at total
  omega

/-- The computed body state is a prefix of the actual initialized macro,
following its setup in the same run with no host reset or later-state input. -/
theorem whole_prefix (mode : Mode) (p : Params) (state : StringExecution.State mode) (first : List Nat) :
    StringWrites.run mode
      ((StringSetup.forms mode p.start p.source p.destination).map (StringWrites.liftString mode)++
        (StringMoves.forms mode first).map (StringWrites.liftString mode)) state=reached mode p state first := by
  simp only [StringWrites.run_append,StringWrites.run_lift_string,reached,setup]

end SmcTuring.Native.StringMacroCopyPrefixes

module
public import SmcTuring.Appendix.Listing8LoopStateValues
public import SmcTuring.Appendix.Listing8DirectionBodyFrames

public section
namespace SmcTuring.Appendix.Listing8LoopStateFrames
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopState.Bounds
abbrev Current:=Listing8LoopState.Current

theorem head_frame (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    MixedMemory.getWord mode (Listing8LoopState.finish mode l t v state).principal.memory l.input.cursor=
      MixedMemory.getWord mode (Listing8LoopHead.finish mode l t v state).principal.memory l.input.cursor := by
  have before := (Listing8StateGeometry.local_bounds mode l t b.head.input.input.prefixBounds.resources b.state).cursorBefore
  have first := Listing8StateFields.first_cursor_before mode l t b.state
  have helpers : ∀ writer ∈ Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l),
      writer.destination+4 ≤ l.input.cursor ∨ l.input.cursor+mode.wordBytes ≤ writer.destination := by
    intro writer member
    right
    cases mode
    all_goals simp only [Listing8StateLayout.helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl
    all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
      Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at before first ⊢ <;> omega
  have packets : ∀ writer ∈ Listing8StateLayout.packets mode (Listing8StateGeometry.region mode l),
      writer.target+4 ≤ l.input.cursor ∨ l.input.cursor+mode.wordBytes ≤ writer.target := by
    intro writer member
    right
    cases mode
    all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
      Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
      Listing8StateLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes] at before first ⊢ <;> omega
  exact congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes))
    (Listing8StateTrace.window mode (Listing8StateGeometry.region mode l) (Listing8StateGeometry.local_bounds mode l t b.head.input.input.prefixBounds.resources b.state) _
      (Listing8LoopHead.endpoint mode l t v old b.head state entry forward current.head) l.input.cursor mode.wordBytes helpers packets)
theorem direction_fragments (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l) (Listing8LoopState.finish mode l t v state).principal.memory :=
  Listing8LoopDirectionImage.transport mode _ _ _ (Listing8LoopHead.current_after mode l t v old b.head state entry forward current.head)
    (fun w member => Listing8StateTrace.window mode _
      (Listing8StateGeometry.local_bounds mode l t b.head.input.input.prefixBounds.resources b.state) _
      (Listing8LoopHead.endpoint mode l t v old b.head state entry forward current.head) w.1 w.2
      (Listing8DirectionBodyFrames.state_helpers_outside mode l w member)
      (Listing8DirectionBodyFrames.state_packets_outside mode l b.head.input.input.prefixBounds.resources w member))

theorem window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory)
    (observed count : Nat) (helpers : ∀ writer∈Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l),
      writer.destination+4≤observed ∨ observed+count≤writer.destination)
    (packets : ∀ writer∈Listing8StateLayout.packets mode (Listing8StateGeometry.region mode l),
      writer.target+4≤observed ∨ observed+count≤writer.target) :
    ByteMemory.bytesAt (Listing8LoopState.finish mode l t v state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8LoopHead.finish mode l t v state).principal.memory observed count :=
  Listing8StateTrace.window mode _ (Listing8StateGeometry.local_bounds mode l t b.head.input.input.prefixBounds.resources b.state) _
    (Listing8LoopHead.endpoint mode l t v old b.head state entry forward current.head) observed count helpers packets

end SmcTuring.Appendix.Listing8LoopStateFrames

module
public import SmcTuring.Appendix.Listing8LoopFailureFrames
public import SmcTuring.Appendix.Listing8EarlyState

public section
namespace SmcTuring.Appendix.Listing8LoopEarlyFrames
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopFailure.Bounds
abbrev Current:=Listing8LoopFailure.Current

theorem main_prefix (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤l.start) :
    ByteMemory.bytesAt (Listing8MainPrefix.finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  have bounds:=b.state.head.input.input.prefixBounds
  have patch:=Listing8EarlyOwners.patch_after mode l
  have input:=Listing8EarlyOwners.input_after mode l bounds.resources
  have d:=destinations mode l
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have direction:=bounds.owners.directionAfter
  have inputEnd : l.input.start≤Listing8LiteralInput.endPC mode l.input := by
    have coords:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  apply Listing8MainPrefixFrames.window mode l t v bounds state entry forward current.state.head.input.prefixCurrent observed count
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · intro site member
    have located:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).1
    change patchStart mode l+40≤site.owner at located
    exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · exact Or.inr (Nat.le_trans before (Listing8EarlyGeometry.second_cursor mode l))
  · intro writer member
    exact Or.inr (Nat.le_trans before (Listing8EarlyGeometry.pointer_targets mode l t bounds.copies writer member))

theorem input (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤l.start)
    (tapeOutside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8MainInput.finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [Listing8MainInputFrames.input_window mode l t v old b.state.head.input state entry forward current.state.head.input observed count
    (Listing8EarlyStages.input_outside mode l t b.state.head.input.input.prefixBounds.resources b.failure.state.head.input observed count before tapeOutside)]
  exact main_prefix mode l t v sentinel begin old b state entry forward current observed count before

theorem direction (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤l.start)
    (tapeOutside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8LoopDirection.finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [Listing8LoopDirection.finish,Listing8DirectionTrace.window mode _ b.state.head.direction.capacity _
    (Listing8MainInput.endpoint mode l t v old b.state.head.input state entry forward current.state.head.input) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.direction_helpers mode l t b.state.head.direction writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.direction_packets mode l t b.state.head.direction writer member)))]
  exact input mode l t v sentinel begin old b state entry forward current observed count before tapeOutside

theorem head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤l.start)
    (tapeOutside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8LoopHead.finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [Listing8LoopHead.finish,Listing8HeadTailTrace.window mode _ (Listing8HeadGeometry.tail_bounds mode l t b.state.head.direction) _
    (Listing8LoopDirection.endpoint mode l t v old b.state.head state entry forward current.state.head) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.tail_xors mode l t b.state.head.direction writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.tail_packets mode l t b.state.head.direction writer (List.mem_append_left _ member))))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.tail_packets mode l t b.state.head.direction writer (List.mem_append_right _ member))))]
  exact direction mode l t v sentinel begin old b state entry forward current observed count before tapeOutside

theorem state (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤l.start)
    (tapeOutside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8LoopState.finish mode l t v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [Listing8LoopState.finish,Listing8StateTrace.window mode _ (Listing8StateGeometry.local_bounds mode l t b.state.head.input.input.prefixBounds.resources b.state.state) _
    (Listing8LoopHead.endpoint mode l t v old b.state.head state entry forward current.state.head) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyState.state_helpers mode l t b.state.state writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyState.state_packets mode l t b.state.state writer member)))]
  exact head mode l t v sentinel begin old b state entry forward current observed count before tapeOutside

theorem failure (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤l.start)
    (tapeOutside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t v sentinel begin state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  have mainBefore : l.start≤(Listing8FailureGeometry.region mode l sentinel begin).start := by
    have coords:=(Listing8FailureGeometry.positions mode l t sentinel begin b.failure).1
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  rw [Listing8LoopFailureFrames.before_window mode l t v sentinel begin old b state entry forward current observed count (Nat.le_trans before mainBefore)]
  exact Listing8LoopEarlyFrames.state mode l t v sentinel begin old b state entry forward current observed count before tapeOutside

end SmcTuring.Appendix.Listing8LoopEarlyFrames

module
public import SmcTuring.Appendix.Listing8LoopFailureFrames
public import SmcTuring.Appendix.Listing8LoopInputBodyGeometry

public section
namespace SmcTuring.Appendix.Listing8LoopInputBodyFrames
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopFailure.Bounds
abbrev Current:=Listing8LoopFailure.Current

theorem direction (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (image : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤Listing8LiteralInput.endPC mode l.input)
    (secondOutside : (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤observed ∨ observed+count≤(Listing8StateGeometry.region mode l).cursor)
    (firstOutside : l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor) :
    ByteMemory.bytesAt (Listing8LoopDirection.finish mode l t v state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8MainInput.finish mode l t v state).principal.memory observed count :=
  Listing8LoopDirection.window mode l t v old b.state.head state entry forward image.state.head observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8LoopInputBodyGeometry.direction_helpers mode l t b.state.head.direction writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8LoopInputBodyGeometry.direction_packets mode l t b.state.head.direction writer member)))

theorem head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (image : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤Listing8LiteralInput.endPC mode l.input)
    (secondOutside : (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤observed ∨ observed+count≤(Listing8StateGeometry.region mode l).cursor)
    (firstOutside : l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor) :
    ByteMemory.bytesAt (Listing8LoopHead.finish mode l t v state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8MainInput.finish mode l t v state).principal.memory observed count := by
  rw [Listing8LoopHead.finish,Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t b.state.head.direction) _
    (Listing8LoopDirection.endpoint mode l t v old b.state.head state entry forward image.state.head) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8LoopInputBodyGeometry.tail_xors mode l t b.state.head.direction writer member)))
    (fun writer member => Listing8LoopInputBodyGeometry.tail_packets mode l t b.state.head.direction observed count before firstOutside writer (List.mem_append_left _ member))
    (fun writer member => Listing8LoopInputBodyGeometry.tail_packets mode l t b.state.head.direction observed count before firstOutside writer (List.mem_append_right _ member))]
  exact direction mode l t v sentinel begin old b state entry forward image observed count before secondOutside firstOutside

theorem state_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (image : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤Listing8LiteralInput.endPC mode l.input)
    (secondOutside : (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤observed ∨ observed+count≤(Listing8StateGeometry.region mode l).cursor)
    (firstOutside : l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor) :
    ByteMemory.bytesAt (Listing8LoopState.finish mode l t v state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8MainInput.finish mode l t v state).principal.memory observed count := by
  rw [Listing8LoopStateFrames.window mode l t v old b.state state entry forward image.state observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8LoopInputBodyGeometry.state_helpers mode l t b.state.state writer member)))
    (fun writer member => Listing8LoopInputBodyGeometry.state_packets mode l t b.state.state observed count before secondOutside writer member)]
  exact head mode l t v sentinel begin old b state entry forward image observed count before secondOutside firstOutside

theorem failure (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (image : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat) (before : observed+count≤Listing8LiteralInput.endPC mode l.input)
    (secondOutside : (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤observed ∨ observed+count≤(Listing8StateGeometry.region mode l).cursor)
    (firstOutside : l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t v sentinel begin state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8MainInput.finish mode l t v state).principal.memory observed count := by
  rw [Listing8LoopFailureFrames.before_window mode l t v sentinel begin old b state entry forward image observed count
    (Nat.le_trans before (Nat.le_trans (Listing8LoopInputBodyGeometry.state_start mode l t b.state.state) (Listing8FailureFrames.state_before mode l sentinel begin)))]
  exact state_window mode l t v sentinel begin old b state entry forward image observed count before secondOutside firstOutside

end SmcTuring.Appendix.Listing8LoopInputBodyFrames

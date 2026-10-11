module
public import SmcTuring.Appendix.Listing8GraphNextEarlyPrefix

public section
namespace SmcTuring.Appendix.Listing8GraphNextEarlyBody
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤l.start) :
    ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  have resources:=Listing8GraphNextCopies.resources mode origin l t g node rule target ctx
  have bounds:=Listing8GraphNextDirectionBounds.direction mode origin l t g node rule target ctx
  have codeBefore:=Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have main:=code_length mode l
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule)
  have tape : (nextLayout mode origin l g node rule target).sourceNode+10≤observed ∨ observed+count≤(nextLayout mode origin l g node rule target).sourceNode+6 := by
    right;change observed+count≤nodePC mode origin g (Listing8GraphStep.nextNode g node rule)+6;omega
  have disjoint:=Listing8EarlyStages.input_outside mode (nextLayout mode origin l g node rule target) t resources bounds.input observed count before tape
  have frame:=Listing8InputWindows.window mode (nextLayout mode origin l g node rule target).input
    (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
    (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
    ctx.resources.inputFits (Listing8InputBounds.masks mode (nextLayout mode origin l g node rule target)
      (Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx))
    (Listing8GraphNextInputBounds.update mode origin l t g node rule target ctx) (Listing8GraphNextInputBounds.outside mode origin l t g node rule target ctx) _
    (Listing8GraphNextPointers.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextInputImage.current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.head_cursor mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.tape_symbol mode origin l t g node rule target ctx selected memory seed) observed count disjoint
  rw [show ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed count=_ from frame]
  exact Listing8GraphNextEarlyPrefix.pointers mode origin l t g node rule target ctx selected memory seed observed count before

theorem direction (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤l.start) :
    ByteMemory.bytesAt (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  rw [Listing8GraphNextDirection.finish,Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) ctx.body.state.head.capacity _
    (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.direction_helpers mode l t ctx.body.state.head writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.direction_packets mode l t ctx.body.state.head writer member)))]
  exact input mode origin l t g node rule target ctx selected memory seed observed count before

theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤l.start) :
    ByteMemory.bytesAt (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  rw [Listing8GraphNextHead.finish,Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) _
    (Listing8GraphNextDirection.endpoint mode origin l t g node rule target ctx selected memory seed) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.tail_xors mode l t ctx.body.state.head writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.tail_packets mode l t ctx.body.state.head writer (List.mem_append_left _ member))))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.tail_packets mode l t ctx.body.state.head writer (List.mem_append_right _ member))))]
  exact direction mode origin l t g node rule target ctx selected memory seed observed count before

theorem state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤l.start) :
    ByteMemory.bytesAt (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  rw [Listing8GraphNextState.finish,Listing8StateTrace.window mode (Listing8StateGeometry.region mode l) (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state) _
    (Listing8GraphNextHead.endpoint mode origin l t g node rule target ctx selected memory seed) observed count
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyState.state_helpers mode l t ctx.body.state writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyState.state_packets mode l t ctx.body.state writer member)))]
  exact head mode origin l t g node rule target ctx selected memory seed observed count before

theorem failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤l.start) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  have mainBefore : l.start≤(Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start := by
    have coords:=(Listing8FailureGeometry.positions mode l t _ _ ctx.body).1
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  rw [Listing8GraphNextFailureFrames.before_window mode origin l t g node rule target ctx selected memory seed observed count (Nat.le_trans before mainBefore)]
  exact state mode origin l t g node rule target ctx selected memory seed observed count before

end SmcTuring.Appendix.Listing8GraphNextEarlyBody

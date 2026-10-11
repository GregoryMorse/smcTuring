module
public import SmcTuring.Appendix.Listing8GraphNextPointerValues

public section
namespace SmcTuring.Appendix.Listing8GraphNextPointerFrames
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets

theorem failure_before_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤
      Listing8FullTableImage.start mode origin := by
  rw [(Listing8FailureGeometry.positions mode l t _ _ ctx.body).1,ctx.boot.packed,Listing8FullTableImage.start,Listing8FailLayout.end_offset]
  cases mode <;> simp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size] <;> omega

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : Listing8FullTableImage.start mode origin≤observed) :
    ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  have codeBefore:=Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have cursor:=Listing8PointerCopies.cursor_before mode l
  change ByteMemory.bytesAt (Listing8PointerCopies.finish mode l t (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed)).principal.memory observed count= _
  rw [Listing8PointerCopies.window_frame mode l t ctx.copies _
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1 observed count
    (Or.inl (by omega)) (fun writer member => Or.inl (Listing8FailureGeometry.pointer_outside mode l t _ _ ctx.body observed
      (Nat.le_trans (failure_before_table mode origin l t g node rule ctx) after) writer member))]
  exact Listing8GraphNextOwnerFrames.window mode origin l t g node rule target ctx selected memory seed observed count after

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory := by
  have inputBefore:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions)
    (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,window mode origin l t g node rule target ctx selected memory seed _ _ inputBefore]
    exact Listing8GraphBackedgeSources.nodes_initial mode origin l t g node rule ctx memory seed
  · rw [Listing8TransitionTable.Initial,window mode origin l t g node rule target ctx selected memory seed _ _ (Nat.le_refl _)]
    exact Listing8GraphBackedgeSources.table_current mode origin l t g node rule ctx memory seed

theorem source_node (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let next:=nextLayout mode origin l g node rule target
    let v:=Listing8GraphNextRetarget.liveValues mode origin g node rule target
    ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory
      next.sourceNode (sourceNodeBytes mode next v).length=sourceNodeBytes mode next v := by
  have before:=Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule)
  dsimp only
  rw [window mode origin l t g node rule target ctx selected memory seed
    (nextLayout mode origin l g node rule target).sourceNode
    (sourceNodeBytes mode (nextLayout mode origin l g node rule target) (Listing8GraphNextRetarget.liveValues mode origin g node rule target)).length before]
  have prior:=Listing8GraphNextCopies.source_packets mode origin l t g node rule target ctx memory seed
  simpa only [sourceNodeBytes,node_length,Listing8GraphNextRetarget.liveValues] using prior.1

theorem tape_symbol (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory
      ((nextLayout mode origin l g node rule target).sourceNode+6)=(Listing8GraphNextRetarget.liveValues mode origin g node rule target).tape :=
  (node_values mode _ _ _ _ _ (source_node mode origin l t g node rule target ctx selected memory seed)).1

theorem owner_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) := by
  have geometry:=Listing8Initializer.code_geometry mode l
  have cursorEnd : l.input.cursor+mode.wordBytes≤patchStart mode l+40 := by
    rw [ctx.body.state.head.input.fields.cursorLabel]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,StringCodec.sourceField,StringCodec.fieldOffset,Mode.wordBytes] at geometry ⊢ <;> omega
  have afterInput:=Listing8MainOwners.input_after mode l ctx.resources
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have fields:=Listing8CopiedOwners.scalar_bounds mode l
  have direction:=ctx.fields.directionAfter
  have endInput : l.input.start≤Listing8LiteralInput.endPC mode l.input := by
    have input:=Listing8LiteralInput.positions mode l.input
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input <;> omega
  unfold MixedMemory.getWord
  rw [Listing8GraphNextOwnerFrames.live_frame mode origin l t g node rule target ctx selected memory seed l.input.cursor mode.wordBytes
    (fun site member => Or.inr (by
      have bounds:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).1
      change patchStart mode l+40≤site.owner at bounds;omega))
    (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))]
  have d:=destinations mode (nextLayout mode origin l g node rule target)
  have nodePC : (nodeParams mode (nextLayout mode origin l g node rule target)).destination=patchStart mode l+40 := rfl
  rw [Listing8GraphNextCopies.effect mode origin l t g node rule target ctx selected memory seed,
    byte_frame _ _ _ _ _ (Or.inr (by omega)),byte_frame _ _ _ _ _ (Or.inr (by omega))]
  exact Listing8GraphBackedgeValues.head_cursor mode origin l t g node rule ctx memory seed

theorem head_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) := by
  have firstEnd:=StringCodec.field_end mode l.start
  have firstBody : StringCodec.bodyStart mode l.start≤secondStart mode l := by
    unfold secondStart StringCodec.endpoint StringCodec.bodyEnd;omega
  have cursorStart : secondStart mode l≤(Listing8PointerCopies.word mode l).destination := by
    simp only [Listing8PointerCopies.word,StringCodec.sourceField];omega
  have prior:=cursor_end mode l
  have codeAfter:=(coordinates mode l).2.2
  have whole:=(Listing8PointerCopies.sizes mode l t).2.1
  have window:=Listing8PointerCopies.window_frame mode l t ctx.copies
    (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed)
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1
    (StringCodec.sourceField mode l.start) mode.wordBytes
    (Or.inr (by unfold StringCodec.bodyStart at firstBody;omega))
    (fun lay member => Or.inr (by
      have after:=Listing8PointerCopies.destination_after mode l t ctx.copies lay member;omega))
  change MixedMemory.getWord mode (Listing8PointerCopies.finish mode l t (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed)).principal.memory l.input.cursor= _
  rw [ctx.body.state.head.input.fields.cursorLabel] at ⊢
  unfold MixedMemory.getWord
  rw [window]
  have current:=owner_cursor mode origin l t g node rule target ctx selected memory seed
  rw [ctx.body.state.head.input.fields.cursorLabel] at current
  exact current

end SmcTuring.Appendix.Listing8GraphNextPointerFrames

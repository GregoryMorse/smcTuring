module
public import SmcTuring.Appendix.Listing8GraphNextDirectionSelection

public section
namespace SmcTuring.Appendix.Listing8GraphNextHeadEntry
open Native Listing8CopyImage Listing8DirectionGeometry Listing8HeadGeometry Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem input_mask (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed : Nat) (field : observed∈maskFields mode (Listing8DirectionGeometry.region mode l)) :
    DwordCode.get (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed=InputUpdate.mask (Listing8LiteralInput.chosen (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape) := by
  have placed : observed∈(Listing8LiteralInput.distributionLayouts mode (nextLayout mode origin l g node rule target).input).map (fun helper => helper.destination) := by
    change observed∈(Listing8LiteralInput.distributionLayouts mode l.input).map (fun helper => helper.destination)
    simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts]
    rw [ctx.body.state.head.mask]
    cases mode
    all_goals simp only [maskFields,List.mem_cons,List.not_mem_nil,or_false] at field
    all_goals rcases field with rfl | rfl
    all_goals simp
  rcases List.mem_map.mp placed with ⟨reader,member,hit⟩
  rw [←hit]
  exact Listing8GraphNextInputFrames.masks mode origin l t g node rule target ctx selected memory seed reader member

theorem mask (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed : Nat) (field : observed∈maskFields mode (Listing8DirectionGeometry.region mode l)) :
    DwordCode.get (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory observed=InputUpdate.mask (Listing8LiteralInput.chosen (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape) := by
  have frame:=Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) ctx.body.state.head.capacity (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed)
    (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed) observed 4 (mask_helpers mode (Listing8DirectionGeometry.region mode l) observed field) (mask_packets mode (Listing8DirectionGeometry.region mode l) observed field)
  have kept:=congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) frame
  change DwordCode.get (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory observed=DwordCode.get (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed at kept
  rw [kept]
  exact input_mask mode origin l t g node rule target ctx selected memory seed observed field

theorem input_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=Arithmetic.encodeNat mode (nextLayout mode origin l g node rule target).sourceNode := by
  have disjoint:=cursor_input_outside mode (nextLayout mode origin l g node rule target) t (Listing8GraphNextCopies.resources mode origin l t g node rule target ctx)
    (Listing8GraphNextDirectionBounds.direction mode origin l t g node rule target ctx)
  have frame:=Listing8InputWindows.window mode (nextLayout mode origin l g node rule target).input
    (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
    (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
    ctx.resources.inputFits (Listing8InputBounds.masks mode (nextLayout mode origin l g node rule target)
      (Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx))
    (Listing8GraphNextInputBounds.update mode origin l t g node rule target ctx) (Listing8GraphNextInputBounds.outside mode origin l t g node rule target ctx) _
    (Listing8GraphNextPointers.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextInputImage.current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.head_cursor mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.tape_symbol mode origin l t g node rule target ctx selected memory seed) l.input.cursor mode.wordBytes disjoint
  have kept:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes)) frame
  change MixedMemory.getWord mode (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
    MixedMemory.getWord mode (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor at kept
  rw [kept]
  exact Listing8GraphNextPointerFrames.head_cursor mode origin l t g node rule target ctx selected memory seed

theorem cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=Arithmetic.encodeNat mode (nextLayout mode origin l g node rule target).sourceNode := by
  have frame:=Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) ctx.body.state.head.capacity (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed)
    (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed) l.input.cursor mode.wordBytes
    (cursor_helpers mode (Listing8DirectionGeometry.region mode l) (tail_bounds mode l t ctx.body.state.head))
    (cursor_packets mode (Listing8DirectionGeometry.region mode l) (tail_bounds mode l t ctx.body.state.head))
  have kept:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes)) frame
  change MixedMemory.getWord mode (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=MixedMemory.getWord mode (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor at kept
  rw [kept]
  exact input_cursor mode origin l t g node rule target ctx selected memory seed

end SmcTuring.Appendix.Listing8GraphNextHeadEntry

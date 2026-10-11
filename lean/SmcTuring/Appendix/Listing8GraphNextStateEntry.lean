module
public import SmcTuring.Appendix.Listing8GraphNextState

public section
namespace SmcTuring.Appendix.Listing8GraphNextStateEntry
open Native Listing8CopyImage Listing8StateGeometry Listing8StateFields Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem new_frame (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed : Nat) (member : observed∈newFields mode (Listing8StateGeometry.region mode l)) :
    DwordCode.get (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory observed=
      DwordCode.get (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory observed := by
  have spans:=field_span mode (Listing8StateGeometry.region mode l) observed (List.mem_append_left _ member)
  have headFrame:=Listing8GraphNextHeadFrames.head_window mode origin l t g node rule target ctx selected memory seed observed 4 spans.1
  have disjoint:=new_input_outside mode (nextLayout mode origin l g node rule target) t (Listing8GraphNextDirectionBounds.state mode origin l t g node rule target ctx) observed member
  have inputFrame:=Listing8InputWindows.window mode (nextLayout mode origin l g node rule target).input
    (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
    (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
    ctx.resources.inputFits (Listing8InputBounds.masks mode (nextLayout mode origin l g node rule target)
      (Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx))
    (Listing8GraphNextInputBounds.update mode origin l t g node rule target ctx) (Listing8GraphNextInputBounds.outside mode origin l t g node rule target ctx) _
    (Listing8GraphNextPointers.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextInputImage.current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.head_cursor mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.tape_symbol mode origin l t g node rule target ctx selected memory seed) observed 4 disjoint
  exact congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) (headFrame.trans inputFrame)

theorem new_low (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateLayout.newPC mode (Listing8StateGeometry.region mode l)+6)=Listing8DirectionFields.low mode (liveValues mode origin g node rule target).newState := by
  rw [new_frame mode origin l t g node rule target ctx selected memory seed _ (by cases mode <;> simp [newFields]),←ctx.body.state.state,
    Listing8GraphNextPointerValues.memory_effect mode origin l t g node rule target ctx selected memory seed,
    Listing8DirectionFields.pointer_frame mode _ t.forward (liveValues mode origin g node rule target).forward (t.state+6)
      (Or.inl (Listing8StateEntryValues.neighbor_before mode l t ctx.body.state t.forward (by simp))),
    Listing8DirectionFields.pointer_frame mode _ t.back (liveValues mode origin g node rule target).back (t.state+6)
      (Or.inl (Listing8StateEntryValues.neighbor_before mode l t ctx.body.state t.back (by simp))),Listing8DirectionFields.pointer_low]

theorem new_high (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context .x64 origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State .x64) :
    DwordCode.get (Listing8GraphNextHead.finish .x64 origin l t g node rule target memory seed).principal.memory (Listing8StateLayout.newPC .x64 (Listing8StateGeometry.region .x64 l)+16)=X64.HalfWords.high (liveValues .x64 origin g node rule target).newState := by
  have forward:=Listing8StateEntryValues.neighbor_before .x64 l t ctx.body.state t.forward (by simp)
  have back:=Listing8StateEntryValues.neighbor_before .x64 l t ctx.body.state t.back (by simp)
  simp only [reduceCtorEq,ite_false] at forward back
  rw [new_frame .x64 origin l t g node rule target ctx selected memory seed _ (by simp [newFields]),←ctx.body.state.state,
    Listing8GraphNextPointerValues.memory_effect .x64 origin l t g node rule target ctx selected memory seed,
    Listing8DirectionFields.pointer_frame .x64 _ t.forward (liveValues .x64 origin g node rule target).forward (t.state+16) (Or.inl (by simp only [reduceCtorEq,ite_false];omega)),
    Listing8DirectionFields.pointer_frame .x64 _ t.back (liveValues .x64 origin g node rule target).back (t.state+16) (Or.inl (by simp only [reduceCtorEq,ite_false];omega)),Listing8DirectionFields.pointer_high]

theorem mask (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed : Nat) (field : observed∈maskFields mode (Listing8StateGeometry.region mode l)) :
    DwordCode.get (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory observed=InputUpdate.mask (Listing8LiteralInput.chosen (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape) := by
  have spans:=field_span mode (Listing8StateGeometry.region mode l) observed (List.mem_append_right _ field)
  have frame:=Listing8GraphNextHeadFrames.head_window mode origin l t g node rule target ctx selected memory seed observed 4 spans.1
  have kept:=congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) frame
  change DwordCode.get (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory observed=
    DwordCode.get (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed at kept
  rw [kept]
  have placed : observed∈(Listing8LiteralInput.distributionLayouts mode (nextLayout mode origin l g node rule target).input).map (fun helper => helper.destination) := by
    change observed∈(Listing8LiteralInput.distributionLayouts mode l.input).map (fun helper => helper.destination)
    simp only [Listing8LiteralInput.distributionLayouts,Listing8MaskCopy.distributionLayouts]
    rw [ctx.body.state.mask]
    cases mode
    all_goals simp only [maskFields,List.mem_cons,List.not_mem_nil,or_false] at field
    all_goals rcases field with rfl | rfl
    all_goals simp
  rcases List.mem_map.mp placed with ⟨reader,member,hit⟩
  rw [←hit]
  exact Listing8GraphNextInputFrames.masks mode origin l t g node rule target ctx selected memory seed reader member

theorem cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=(liveValues mode origin g node rule target).next := by
  have tail:=Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed)
    (Listing8GraphNextDirection.endpoint mode origin l t g node rule target ctx selected memory seed) (Listing8StateGeometry.region mode l).cursor mode.wordBytes
    (cursor_tail_xors mode l t ctx.resources ctx.body.state)
    (fun writer member => cursor_tail_packets mode l t ctx.resources ctx.body.state writer (List.mem_append_left _ member))
    (fun writer member => cursor_tail_packets mode l t ctx.resources ctx.body.state writer (List.mem_append_right _ member))
  have direction:=Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) ctx.body.state.head.capacity
    (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed) (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed) (Listing8StateGeometry.region mode l).cursor mode.wordBytes
    (cursor_selection_helpers mode l t ctx.resources ctx.body.state) (cursor_selection_packets mode l t ctx.resources ctx.body.state)
  have disjoint:=cursor_input_outside mode (nextLayout mode origin l g node rule target) t (Listing8GraphNextCopies.resources mode origin l t g node rule target ctx) (Listing8GraphNextDirectionBounds.state mode origin l t g node rule target ctx)
  have inputFrame:=Listing8InputWindows.window mode (nextLayout mode origin l g node rule target).input
    (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
    (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
    ctx.resources.inputFits (Listing8InputBounds.masks mode (nextLayout mode origin l g node rule target)
      (Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx))
    (Listing8GraphNextInputBounds.update mode origin l t g node rule target ctx) (Listing8GraphNextInputBounds.outside mode origin l t g node rule target ctx) _
    (Listing8GraphNextPointers.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextInputImage.current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.head_cursor mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.tape_symbol mode origin l t g node rule target ctx selected memory seed) (Listing8StateGeometry.region mode l).cursor mode.wordBytes disjoint
  have kept:=congrArg (fun bytes => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack bytes)) ((tail.trans direction).trans inputFrame)
  change MixedMemory.getWord mode (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
    MixedMemory.getWord mode (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor at kept
  rw [kept]
  exact Listing8GraphNextPointerValues.transition_cursor mode origin l t g node rule target ctx selected memory seed

end SmcTuring.Appendix.Listing8GraphNextStateEntry

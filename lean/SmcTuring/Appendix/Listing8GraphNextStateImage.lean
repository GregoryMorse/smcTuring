module
public import SmcTuring.Appendix.Listing8StateReuseFrames

public section
namespace SmcTuring.Appendix.Listing8GraphNextStateImage
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def previousExtra (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8FailureGlobalImage.backing mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory)
@[expose] def previousState (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalState.entryState mode l t (values mode origin g node rule) (previousExtra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed)

theorem code_before (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) : codeEnd mode l≤w.1 := by
  have lower:=(Listing8StateGeometry.window_span mode (Listing8StateGeometry.region mode l) w member).1
  have state:=(Listing8StateGeometry.positions mode l t ctx.body.state).1
  have input:=(Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined).2.1
  have after:=ctx.resources.inputAfter
  have endInput:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at state input endInput <;> omega

theorem after_backedge (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (previousState mode origin l t g node rule memory seed).principal.memory w.1 w.2 := by
  rw [Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  exact Listing8StateReuseFrames.failure mode l t (values mode origin g node rule) _ _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body (extra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed) w member

theorem after_owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory w.1 w.2 := by
  have codeBefore:=code_before mode origin l t g node rule target ctx selected memory seed w member
  have spans:=Listing8StateGeometry.window_span mode (Listing8StateGeometry.region mode l) w member
  have state:=(Listing8StateGeometry.positions mode l t ctx.body.state).1
  have input:=(Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined).2.1
  have lower : Listing8LiteralInput.endPC mode l.input≤w.1 := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at state input <;> omega
  have fields:=Listing8CopiedOwners.scalar_bounds mode l
  have source:=Listing8OwnerImage.source_field_bounds mode l
  rw [Listing8GraphNextOwnerFrames.live_frame mode origin l t g node rule target ctx selected memory seed w.1 w.2
    (fun site siteMember => Or.inl (by
      have bounds:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site siteMember).2.1
      change site.owner+10≤codeEnd mode l at bounds;omega))
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    (Or.inl (Listing8StateGeometry.direction_outside mode l t ctx.body.state w.1 spans.1))]
  exact Listing8GraphNextCopyFrames.window mode origin l t g node rule target ctx selected memory seed w.1 w.2 codeBefore

theorem after_pointers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2 := by
  have before:=code_before mode origin l t g node rule target ctx selected memory seed w member
  have cursor:=Listing8PointerCopies.cursor_before mode l
  exact Listing8PointerCopies.window_frame mode l t ctx.copies _
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1 w.1 w.2 (Or.inl (by omega))
    (Listing8StateGeometry.pointer_outside mode l t ctx.body.state w member)

theorem after_input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2 := by
  have disjoint:=Listing8StateGeometry.input_outside mode (nextLayout mode origin l g node rule target) t
    (Listing8GraphNextDirectionBounds.state mode origin l t g node rule target ctx) w member
  exact Listing8InputWindows.window mode (nextLayout mode origin l g node rule target).input
    (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
    (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
    ctx.resources.inputFits (Listing8InputBounds.masks mode (nextLayout mode origin l g node rule target)
      (Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx))
    (Listing8GraphNextInputBounds.update mode origin l t g node rule target ctx) (Listing8GraphNextInputBounds.outside mode origin l t g node rule target ctx) _
    (Listing8GraphNextPointers.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextInputImage.current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.head_cursor mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.tape_symbol mode origin l t g node rule target ctx selected memory seed) w.1 w.2 disjoint

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (previousState mode origin l t g node rule memory seed).principal.memory w.1 w.2 := by
  rw [Listing8GraphNextHeadFrames.head_window mode origin l t g node rule target ctx selected memory seed w.1 w.2 (Listing8StateGeometry.window_span mode _ w member).1,
    after_input mode origin l t g node rule target ctx selected memory seed w member,after_pointers mode origin l t g node rule target ctx selected memory seed w member,after_owners mode origin l t g node rule target ctx selected memory seed w member]
  exact after_backedge mode origin l t g node rule ctx memory seed w member

theorem helper_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).start
      (DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l))).length=
      DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l)) := by
  have member : ((Listing8StateGeometry.region mode l).start,
      (DwordMixedSequence.bytes mode (Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l))).length)∈
      Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l) := by
    cases mode <;> simp [Listing8StateGeometry.windows,DwordMixedSequence.bytes,Listing8StateLayout.helpers,Listing8PointerCopies.split,
      DwordMixedImage.bytes_length,DwordLayout.span,DwordLayout.storeSize]
  rw [current mode origin l t g node rule target ctx selected memory seed _ member]
  exact Listing8StateImage.helper_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state (previousExtra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)

theorem headers_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordPackets.Intact mode (Listing8StateLayout.packets mode (Listing8StateGeometry.region mode l))
      (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory := by
  intro reader readerMember
  have member : (reader.pc,6)∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l) := by
    cases mode
    all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
      Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at readerMember
    all_goals rcases readerMember with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Listing8StateGeometry.windows]
  rw [DwordPackets.Current,current mode origin l t g node rule target ctx selected memory seed _ member]
  exact Listing8StateImage.headers_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state (previousExtra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed) reader readerMember

end SmcTuring.Appendix.Listing8GraphNextStateImage

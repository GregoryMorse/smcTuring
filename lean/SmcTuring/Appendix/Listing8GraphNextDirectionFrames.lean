module
public import SmcTuring.Appendix.Listing8DirectionPrefixFrames
public import SmcTuring.Appendix.Listing8DirectionBodyFrames

public section
namespace SmcTuring.Appendix.Listing8GraphNextDirectionFrames
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def previousExtra (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8StateImage.backing mode l (Listing8FailureGlobalImage.backing mode l (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory))
@[expose] def previousDirection (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalDirection.finish mode l t (values mode origin g node rule) (previousExtra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed)

theorem after_backedge (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (w : Nat × Nat)
    (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (previousDirection mode origin l t g node rule memory seed).principal.memory w.1 w.2 := by
  rw [Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  change ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t (values mode origin g node rule) _ _
    (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory w.1 w.2= _
  rw [Listing8DirectionBodyFrames.failure mode l t (values mode origin g node rule) _ _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body _ _ w member]
  exact (Listing8DirectionBodyFrames.direction mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head (previousExtra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed) w member).symm

theorem after_owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory w.1 w.2 := by
  have codeBefore:=Listing8DirectionPrefixFrames.code_before mode l ctx.resources w member
  have lower:=(Listing8DirectionWindows.window_span mode (Listing8DirectionGeometry.region mode l) w member).1
  change Listing8LiteralInput.endPC mode l.input≤w.1 at lower
  have fields:=Listing8CopiedOwners.scalar_bounds mode l
  have source:=Listing8OwnerImage.source_field_bounds mode l
  rw [Listing8GraphNextOwnerFrames.live_frame mode origin l t g node rule target ctx selected memory seed w.1 w.2
    (fun site siteMember => Or.inl (by
      have bounds:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site siteMember).2.1
      change site.owner+10≤codeEnd mode l at bounds;omega))
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    (Listing8DirectionPrefixFrames.direction_store_outside mode l t ctx.body.state.head w member)]
  exact Listing8GraphNextCopyFrames.window mode origin l t g node rule target ctx selected memory seed w.1 w.2 codeBefore

theorem after_pointers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2 := by
  have codeBefore:=Listing8DirectionPrefixFrames.code_before mode l ctx.resources w member
  have cursor:=Listing8PointerCopies.cursor_before mode l
  exact Listing8PointerCopies.window_frame mode l t ctx.copies _
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1 w.1 w.2
    (Or.inl (by omega)) (Listing8DirectionPrefixFrames.pointer_outside mode l t ctx.body.state.head w member)

theorem after_input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2 := by
  have disjoint:=Listing8DirectionPrefixFrames.input_outside mode (nextLayout mode origin l g node rule target) t
    (Listing8GraphNextDirectionBounds.direction mode origin l t g node rule target ctx) w member
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
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (previousDirection mode origin l t g node rule memory seed).principal.memory w.1 w.2 :=
  (after_input mode origin l t g node rule target ctx selected memory seed w member).trans
    ((after_pointers mode origin l t g node rule target ctx selected memory seed w member).trans
      ((after_owners mode origin l t g node rule target ctx selected memory seed w member).trans
        (after_backedge mode origin l t g node rule ctx memory seed w member)))

end SmcTuring.Appendix.Listing8GraphNextDirectionFrames

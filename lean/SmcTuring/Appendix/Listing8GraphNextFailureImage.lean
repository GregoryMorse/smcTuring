module
public import SmcTuring.Appendix.Listing8GraphNextStateFrames
public import SmcTuring.Appendix.Listing8FailureReuseTransport

public section
namespace SmcTuring.Appendix.Listing8GraphNextFailureImage
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem code_before (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed)
    (upper : observed+count≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5) : codeEnd mode l≤observed := by
  have fail:=(Listing8FailureGeometry.positions mode l t _ _ ctx.body).1
  have input:=(Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined).2.1
  have endInput:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  have before:=ctx.resources.inputAfter
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at fail input endInput <;> omega

theorem after_owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed)
    (upper : observed+count≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5) :
    ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  have codeBefore:=code_before mode origin l t g node rule target ctx selected memory seed observed count after upper
  have stateBefore:=Listing8FailureFrames.state_before mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have headAfter:=Nat.le_trans stateBefore after
  have fail:=(Listing8FailureGeometry.positions mode l t _ _ ctx.body).1
  have input:=(Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined).2.1
  have lower : Listing8LiteralInput.endPC mode l.input≤observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at fail input <;> omega
  have fields:=Listing8CopiedOwners.scalar_bounds mode l
  have source:=Listing8OwnerImage.source_field_bounds mode l
  rw [Listing8GraphNextOwnerFrames.live_frame mode origin l t g node rule target ctx selected memory seed observed count
    (fun site member => Or.inl (by
      have bound:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).2.1
      change site.owner+10≤codeEnd mode l at bound;omega))
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    (Or.inl (Listing8StateGeometry.direction_outside mode l t ctx.body.state observed headAfter))]
  exact Listing8GraphNextCopyFrames.window mode origin l t g node rule target ctx selected memory seed observed count codeBefore

theorem after_pointers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed)
    (upper : observed+count≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5) :
    ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory observed count := by
  have codeBefore:=code_before mode origin l t g node rule target ctx selected memory seed observed count after upper
  have cursor:=Listing8PointerCopies.cursor_before mode l
  exact Listing8PointerCopies.window_frame mode l t ctx.copies _
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1 observed count (Or.inl (by omega))
    (fun writer member => Or.inl (Listing8FailureGeometry.pointer_outside mode l t _ _ ctx.body observed after writer member))

theorem after_input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed)
    (upper : observed+count≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5) :
    ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory observed count := by
  have disjoint:=Listing8FailureGeometry.input_outside mode (nextLayout mode origin l g node rule target) t
    (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
    (Listing8GraphNextDirectionBounds.failure mode origin l t g node rule target ctx) observed count after upper
  exact Listing8InputWindows.window mode (nextLayout mode origin l g node rule target).input
    (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
    (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
    ctx.resources.inputFits (Listing8InputBounds.masks mode (nextLayout mode origin l g node rule target)
      (Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx))
    (Listing8GraphNextInputBounds.update mode origin l t g node rule target ctx) (Listing8GraphNextInputBounds.outside mode origin l t g node rule target ctx) _
    (Listing8GraphNextPointers.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextInputImage.current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.head_cursor mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.tape_symbol mode origin l t g node rule target ctx selected memory seed) observed count disjoint

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed)
    (upper : observed+count≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5) :
    ByteMemory.bytesAt (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  rw [Listing8GraphNextStateFrames.window mode origin l t g node rule target ctx selected memory seed observed count after,
    Listing8GraphNextHeadFrames.head_window mode origin l t g node rule target ctx selected memory seed observed count
      (Nat.le_trans (Listing8FailureFrames.state_before mode l _ _) after),
    after_input mode origin l t g node rule target ctx selected memory seed observed count after upper,after_pointers mode origin l t g node rule target ctx selected memory seed observed count after upper]
  exact after_owners mode origin l t g node rule target ctx selected memory seed observed count after upper

theorem after_backedge (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8FailureReuseImage.Current mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory := by
  have initial:=Listing8FailureGlobalImage.current_region mode l t (values mode origin g node rule) _ _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  have first:=Listing8FailureReuseImage.from_initial mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) _ initial
  have kept:=Listing8FailureReuseEffects.current_after mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GlobalFailure.entry mode l t (values mode origin g node rule) _ _ ctx.resources
      (owners mode origin l t g node rule ctx) ctx.copies ctx.body (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)) first
  rw [Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  exact kept

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8FailureReuseImage.Current mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory := by
  apply Listing8FailureReuseTransport.current mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) _ _ (after_backedge mode origin l t g node rule ctx memory seed)
  intro observed count after beforeEnd
  have before : Listing8FailureLayout.endPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5 := by
    unfold Listing8FailureLayout.callPC;omega
  exact window mode origin l t g node rule target ctx selected memory seed observed count after (Nat.le_trans beforeEnd before)

end SmcTuring.Appendix.Listing8GraphNextFailureImage

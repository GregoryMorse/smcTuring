module
public import SmcTuring.Appendix.Listing8GraphNextBegin

public section
namespace SmcTuring.Appendix.Listing8GraphNextLateBody
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem code_before (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed) : codeEnd mode l≤observed := by
  have fail:=(Listing8FailureGeometry.positions mode l t _ _ ctx.body).1
  have input:=(Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined).2.1
  have endInput:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  have before:=ctx.resources.inputAfter
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at fail input endInput <;> omega

theorem after_owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed) :
    ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  have codeBefore:=code_before mode origin l t g node rule target ctx selected memory seed observed count after
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
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed) :
    ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory observed count := by
  have codeBefore:=code_before mode origin l t g node rule target ctx selected memory seed observed count after
  have cursor:=Listing8PointerCopies.cursor_before mode l
  exact Listing8PointerCopies.window_frame mode l t ctx.copies _
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1 observed count (Or.inl (by omega))
    (fun writer member => Or.inl (Listing8FailureGeometry.pointer_outside mode l t _ _ ctx.body observed after writer member))

theorem after_input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed)
    (tapeOutside : (nextLayout mode origin l g node rule target).sourceNode+10≤observed ∨ observed+count≤(nextLayout mode origin l g node rule target).sourceNode+6) :
    ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory observed count := by
  have disjoint:=Listing8LateFrames.input_outside mode (nextLayout mode origin l g node rule target) t
    (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
    (Listing8GraphNextDirectionBounds.failure mode origin l t g node rule target ctx) observed count after tapeOutside
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

theorem state_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start≤observed)
    (tapeOutside : (nextLayout mode origin l g node rule target).sourceNode+10≤observed ∨ observed+count≤(nextLayout mode origin l g node rule target).sourceNode+6) :
    ByteMemory.bytesAt (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  rw [Listing8GraphNextStateFrames.window mode origin l t g node rule target ctx selected memory seed observed count after,
    Listing8GraphNextHeadFrames.head_window mode origin l t g node rule target ctx selected memory seed observed count
      (Nat.le_trans (Listing8FailureFrames.state_before mode l _ _) after),
    after_input mode origin l t g node rule target ctx selected memory seed observed count after tapeOutside,after_pointers mode origin l t g node rule target ctx selected memory seed observed count after]
  exact after_owners mode origin l t g node rule target ctx selected memory seed observed count after

theorem after_failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat)
    (after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5≤observed)
    (tapeOutside : (nextLayout mode origin l g node rule target).sourceNode+10≤observed ∨ observed+count≤(nextLayout mode origin l g node rule target).sourceNode+6) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  let region:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  change Listing8FailureLayout.callPC mode region+5≤observed at after
  have coords:=Listing8FailureLayout.positions mode region
  have lower : region.start≤observed := by
    cases mode <;> simp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan] at coords after ⊢ <;> omega
  have andBefore : Listing8FailureLayout.andPC mode region+10≤observed := by
    have maskBefore:=coords.2.2.1
    simp only [Listing8FailureLayout.mask,Listing8FailureLayout.xorPC] at maskBefore
    cases mode <;> simp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan] at coords maskBefore after ⊢ <;> omega
  have maskBefore : Listing8FailureLayout.mask mode region+4≤observed := by
    cases mode <;> simp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan] at coords after ⊢ <;> omega
  rw [Listing8GraphNextFailure.finish,Listing8FailureReuseEffects.window mode region
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)
    observed count (Or.inl andBefore) (Or.inl maskBefore) (Or.inl after)]
  exact state_window mode origin l t g node rule target ctx selected memory seed observed count lower tapeOutside

end SmcTuring.Appendix.Listing8GraphNextLateBody

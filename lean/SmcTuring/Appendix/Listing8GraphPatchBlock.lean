module
public import SmcTuring.Appendix.Listing8GraphNextCopyFrames

public section
namespace SmcTuring.Appendix.Listing8GraphPatchBlock
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets

theorem patch_length (mode : Mode) (l : Layout) : (patchBytes mode l).length=40 := by
  rw [patchBytes,DwordRetargetSequence.bytes_length,Listing8ModeOffsets.sites_length]
theorem after_backedge (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory
      (patchStart mode l) 40=patchBytes mode l := by
  have geometry:=Listing8Initializer.code_geometry mode l
  have field:=ctx.body.state.head.input.fields.cursorLabel
  have cursorFirst : l.input.cursor+mode.wordBytes≤patchStart mode l := by
    rw [field]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,StringCodec.sourceField,StringCodec.fieldOffset,Mode.wordBytes] at geometry ⊢ <;> omega
  have cursorSecond : (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤patchStart mode l := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,Listing8StateGeometry.region,StringCodec.sourceField,StringCodec.fieldOffset,Mode.wordBytes] at geometry ⊢ <;> omega
  have lower:=Listing8GraphCopyResources.input_before_node mode origin l t g node rule ctx node
  rw [←ctx.nodeLocated] at lower
  have input:=code_to_input mode l ctx.resources
  have patchBefore : patchStart mode l+40≤codeEnd mode l := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at geometry <;> omega
  rw [Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  change ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t (values mode origin g node rule)
    (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory (patchStart mode l) 40=patchBytes mode l
  rw [Listing8MainState.failure mode l t (values mode origin g node rule) _ _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body (extra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed) _ _ (Nat.le_refl _) (Or.inl cursorSecond) (Or.inl cursorFirst) (Or.inr (by omega))]
  have original:=initial_patches mode l (values mode origin g node rule) ctx.resources (Listing8PointerImage.backing mode l t
    (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l
      (Listing8FailureGlobalImage.backing mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory)))))
  rw [patch_length] at original
  exact original
theorem after_copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed).principal.memory
      (patchStart mode l) 40=patchBytes mode l := by
  have d:=destinations mode (nextLayout mode origin l g node rule target)
  have nodePC : (nodeParams mode (nextLayout mode origin l g node rule target)).destination=patchStart mode l+40 := rfl
  rw [Listing8GraphNextCopies.effect mode origin l t g node rule target ctx selected memory seed,
    byte_frame _ _ _ _ _ (Or.inr (by omega)),byte_frame _ _ _ _ _ (Or.inr (by omega))]
  exact after_backedge mode origin l t g node rule ctx memory seed

/-- The live retarget block is joined to the actual newly copied packets;
no zero prototype, initialized replacement, or future block is assumed. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let next:=nextLayout mode origin l g node rule target
    let v:=values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    ByteMemory.bytesAt (Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed).principal.memory
      (patchStart mode l) (Listing8ModeOffsets.bytes mode (patchLayout mode next) next.sourceNode next.sourceTransition
        v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState).length=
      Listing8ModeOffsets.bytes mode (patchLayout mode next) next.sourceNode next.sourceTransition
        v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState := by
  have packets:=Listing8GraphNextCopies.copied_packets mode origin l t g node rule target ctx selected memory seed
  let next:=nextLayout mode origin l g node rule target
  let v:=values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
  have patches : ByteMemory.bytesAt (Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed).principal.memory
      (patchStart mode next) (patchBytes mode next).length=patchBytes mode next := by
    rw [patch_length]
    exact after_copies mode origin l t g node rule target ctx selected memory seed
  have pair:=ByteWindow.join _ (patchStart mode next) (patchBytes mode next) (sourceNodeBytes mode next v) patches
    (by simpa only [patch_length,nodeParams,patchLayout,Listing8ModeOffsets.nodeEntry] using packets.1)
  have all:=ByteWindow.join _ (patchStart mode next) (patchBytes mode next++sourceNodeBytes mode next v)
    (sourceTransitionBytes mode next v) pair (by
      simpa only [List.length_append,patch_length,sourceNodeBytes,Listing8Prototypes.node_length,transitionParams,
        patchLayout,Listing8ModeOffsets.transitionEntry,Listing8ModeOffsets.nodeEntry,Nat.add_assoc] using packets.2)
  exact all

end SmcTuring.Appendix.Listing8GraphPatchBlock

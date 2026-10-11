module
public import SmcTuring.Appendix.Listing8GapState
public import SmcTuring.Appendix.Listing8GraphNextOwnerFrames

public section
namespace SmcTuring.Appendix.Listing8GraphNextHelperImage
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem helper_upper (mode : Mode) (l : Layout) (t : Targets)
    (joined : l.input.start=Listing8PointerCopies.endPC mode l) :
    codeEnd mode l+(Listing8PointerCopies.bytes mode l t).length≤l.input.start := by
  rw [Listing8PointerCopies.bytes_length,joined]

theorem after_backedge (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory
      (codeEnd mode l) (Listing8PointerCopies.bytes mode l t).length=Listing8PointerCopies.bytes mode l t := by
  have upper:=helper_upper mode l t ctx.body.state.head.input.joined
  have second:=Listing8PointerCopies.cursor_before mode l
  have first:=Listing8InputBounds.cursor_bounds mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources
  have nodeAfter:=Listing8GraphCopyResources.input_before_node mode origin l t g node rule ctx node
  rw [←ctx.nodeLocated] at nodeAfter
  have endInput : l.input.start≤Listing8LiteralInput.endPC mode l.input := by
    have input:=Listing8LiteralInput.positions mode l.input
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input <;> omega
  rw [Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  change ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t (values mode origin g node rule)
    (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory (codeEnd mode l) _= _
  rw [Listing8GapState.failure mode l t (values mode origin g node rule) _ _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body (extra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed) _ _ (Nat.le_refl _) upper (Or.inl second) (Or.inl first.2.1) (Or.inr (by omega))]
  exact Listing8PointerImage.initial_helper mode l t (values mode origin g node rule) ctx.resources ctx.body.state.head.input.joined
    (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l
      (Listing8FailureGlobalImage.backing mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory))))

/-- The complete four-call helper image survives the actual previous body,
backedge, next copies, retargets and all seven next copied owners. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory
      (codeEnd mode l) (Listing8PointerCopies.bytes mode l t).length=Listing8PointerCopies.bytes mode l t := by
  have upper:=helper_upper mode l t ctx.body.state.head.input.joined
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have fields:=Listing8CopiedOwners.scalar_bounds mode l
  have direction:=ctx.fields.directionAfter
  have endInput : l.input.start≤Listing8LiteralInput.endPC mode l.input := by
    have input:=Listing8LiteralInput.positions mode l.input
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input <;> omega
  rw [Listing8GraphNextOwnerFrames.live_frame mode origin l t g node rule target ctx selected memory seed _ _
    (fun site member => Or.inl (by
      have bounds:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).2.1
      change site.owner+10≤codeEnd mode l at bounds;omega))
    (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)),
    Listing8GraphNextCopyFrames.window mode origin l t g node rule target ctx selected memory seed _ _ (Nat.le_refl _)]
  exact after_backedge mode origin l t g node rule ctx memory seed

end SmcTuring.Appendix.Listing8GraphNextHelperImage

module
public import SmcTuring.Appendix.Listing8InputReuse
public import SmcTuring.Appendix.Listing8InputBodyFrames
public import SmcTuring.Appendix.Listing8GraphNextPointers

public section
namespace SmcTuring.Appendix.Listing8GraphBackedgeInput
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def pending (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  CursorEffects.delta (values mode origin g node rule).tape (values mode origin g node rule).fresh
    (Listing8LiteralInput.chosen (values mode origin g node rule).rule (values mode origin g node rule).tape)
@[expose] def mask (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  InputUpdate.mask (Listing8LiteralInput.chosen (values mode origin g node rule).rule (values mode origin g node rule).tape)

theorem after_input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let v:=values mode origin g node rule
    Listing8InputMask.Intact mode l.input (-(v.rule-v.tape)) v.tape (pending mode origin g node rule) v.fresh (mask mode origin g node rule)
      (Listing8InputBodyFrames.inputState mode l t v (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
        (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory := by
  let backing:=Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l
    (Listing8FailureGlobalImage.backing mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory)))
  exact Listing8InputReuse.completed_image mode l.input _ _ force _ force ctx.resources.inputFits
    (Listing8InputBounds.masks mode l ctx.body.state.head.input.fields)
    (Listing8InputBounds.update mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources)
    (Listing8InputBounds.outside mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources) _
    (Listing8GlobalInput.entry mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input
      backing (Listing8GlobalBoot.bodySeed mode origin seed))
    (Listing8GlobalInput.input_image mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input
      backing (Listing8GlobalBoot.bodySeed mode origin seed))
    (Listing8GlobalInput.cursor mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input
      backing (Listing8GlobalBoot.bodySeed mode origin seed))
    (Listing8GlobalInput.symbol mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input
      backing (Listing8GlobalBoot.bodySeed mode origin seed))

/-- The complete input code is recovered on actual returned memory,
including its executed scratch, pending delta and previous live mask. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let v:=values mode origin g node rule
    Listing8InputMask.Intact mode l.input (-(v.rule-v.tape)) v.tape (pending mode origin g node rule) v.fresh (mask mode origin g node rule)
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory := by
  have first:=Listing8InputBounds.cursor_bounds mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources
  have second:=Listing8PointerCopies.cursor_before mode l
  change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤codeEnd mode l at second
  have input:=ctx.resources.inputAfter
  rw [Listing8InputMask.Intact,Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  change ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory l.input.start _= _
  rw [Listing8InputBodyFrames.failure mode l t (values mode origin g node rule) _ _ ctx.resources (owners mode origin l t g node rule ctx)
    ctx.copies ctx.body (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed) _ _
    (by rw [Listing8InputMask.bytes_length]) (Or.inl (by omega)) (Or.inl first.2.2.1)]
  exact after_input mode origin l t g node rule ctx memory seed

end SmcTuring.Appendix.Listing8GraphBackedgeInput

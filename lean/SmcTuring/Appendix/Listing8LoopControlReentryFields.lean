module
public import SmcTuring.Appendix.Listing8LoopControlMacros
public import SmcTuring.Appendix.Listing8LoopInputBodyFrames

public section
namespace SmcTuring.Appendix.Listing8LoopControlReentryFields
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
@[expose] def old (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) : OldInput :=
  let v:=values mode origin g node rule
  ⟨-(v.rule-v.tape),v.tape,CursorEffects.delta v.tape v.fresh (Listing8LiteralInput.chosen v.rule v.tape),v.fresh,
    InputUpdate.mask (Listing8LiteralInput.chosen v.rule v.tape)⟩

theorem cursors_before_code (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤codeEnd mode l ∧ l.input.cursor+mode.wordBytes≤codeEnd mode l := by
  have code:=(coordinates mode l).2.2
  have first:=cursor_end mode l
  have second:=Listing8PointerCopies.cursor_before_patch mode l
  change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤patchStart mode l at second
  rw [ctx.body.state.head.input.fields.cursorLabel]
  omega

theorem patches_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (oldInput : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule oldInput state) :
    ByteMemory.bytesAt (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory (patchStart mode l) (patchBytes mode l).length=patchBytes mode l := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule oldInput state ctx.nodeLocated ctx.ruleLocated image.body
  have length:=(Listing8GraphPatchBlock.patch_length mode l)
  have second:=Listing8PointerCopies.cursor_before_patch mode l
  change (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤patchStart mode l at second
  have first:=cursor_end mode l
  rw [←ctx.body.state.head.input.fields.cursorLabel] at first
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx oldInput state image]
  dsimp only [Listing8LoopControl.failureEnd]
  rw [Listing8LoopPrefixBodyFrames.failure mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) oldInput b state image.body.state.head.graph.entry image.body.state.head.graph.forward input _ _
    (by omega) (Or.inl second) (Or.inl first)]
  exact Listing8MainInputFrames.patches_current mode l t (values mode origin g node rule) oldInput b.state.head.input state image.body.state.head.graph.entry image.body.state.head.graph.forward input.state.head.input

theorem helpers_after_prefix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (oldInput : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule oldInput state) :
    ByteMemory.bytesAt (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory (codeEnd mode l) (Listing8PointerCopies.bytes mode l t).length=Listing8PointerCopies.bytes mode l t := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule oldInput state ctx.nodeLocated ctx.ruleLocated image.body
  have before:=(cursors_before_code mode origin l t g node rule ctx).1
  have extent:=Listing8PointerCopies.bytes_length mode l t
  rw [←ctx.body.state.head.input.joined] at extent
  rw [Listing8MainPrefix.finish,Listing8PointerCopies.window_frame mode l t ctx.copies _
    (Listing8MainLiveOwners.registers mode l (values mode origin g node rule) ctx.resources (owners mode origin l t g node rule ctx) ctx.fields.tapeReach state image.body.state.head.graph.entry image.body.state.head.graph.forward input.state.head.input.prefixCurrent.copying).1
    _ _ (Or.inl before) (fun writer member => Or.inr (by
      have after:=Listing8PointerCopies.destination_after mode l t ctx.copies writer member
      rw [←ctx.body.state.head.input.joined] at after
      omega))]
  exact Listing8MainPrefix.helper_current mode l t (values mode origin g node rule) b.state.head.input.input.prefixBounds state image.body.state.head.graph.entry image.body.state.head.graph.forward input.state.head.input.prefixCurrent

theorem helpers_after_input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (oldInput : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule oldInput state) :
    ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory (codeEnd mode l) (Listing8PointerCopies.bytes mode l t).length=Listing8PointerCopies.bytes mode l t := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule oldInput state ctx.nodeLocated ctx.ruleLocated image.body
  have extent:=Listing8PointerCopies.bytes_length mode l t
  rw [←ctx.body.state.head.input.joined] at extent
  have fields:=Listing8LiteralComposition.field_bounds mode l.input
  have nodeAfter:=Listing8GraphCopyResources.input_before_node mode origin l t g node rule ctx node
  rw [←ctx.nodeLocated,←ctx.body.state.head.input.fields.headLabel] at nodeAfter
  rw [Listing8MainInputFrames.input_window mode l t (values mode origin g node rule) oldInput b.state.head.input state image.body.state.head.graph.entry image.body.state.head.graph.forward input.state.head.input _ _
    ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega),Or.inr (by omega),fun writer member => Or.inr (by
      have after:=ctx.body.state.head.input.fields.masksAfter writer member
      have inputEnd:=Listing8OwnerImage.source_field_bounds mode l
      omega)⟩]
  exact helpers_after_prefix mode origin l t g node rule ctx oldInput state image

theorem helpers_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (oldInput : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule oldInput state) :
    ByteMemory.bytesAt (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory (codeEnd mode l) (Listing8PointerCopies.bytes mode l t).length=Listing8PointerCopies.bytes mode l t := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule oldInput state ctx.nodeLocated ctx.ruleLocated image.body
  have extent:=Listing8PointerCopies.bytes_length mode l t
  rw [←ctx.body.state.head.input.joined] at extent
  have inputEnd:=Listing8OwnerImage.source_field_bounds mode l
  have cursors:=cursors_before_code mode origin l t g node rule ctx
  rw [Listing8LoopControl.memory mode origin l t g node rule ctx oldInput state image]
  dsimp only [Listing8LoopControl.failureEnd]
  rw [Listing8LoopInputBodyFrames.failure mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) oldInput b state image.body.state.head.graph.entry image.body.state.head.graph.forward input _ _
    (by omega) (Or.inl cursors.1) (Or.inl cursors.2)]
  exact helpers_after_input mode origin l t g node rule ctx oldInput state image

theorem input_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (oldInput : OldInput) (state : StringExecution.State mode) (image : Listing8LoopControl.Current mode origin l t g node rule oldInput state) :
    Listing8InputMask.Intact mode l.input (old mode origin g node rule).rule (old mode origin g node rule).tape (old mode origin g node rule).pending (old mode origin g node rule).fresh (old mode origin g node rule).mask (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have input:=Listing8LoopGraphFailure.input_current mode origin l t g node rule oldInput state ctx.nodeLocated ctx.ruleLocated image.body
  have extent:=Listing8InputMask.bytes_length mode l.input (old mode origin g node rule).rule (old mode origin g node rule).tape (old mode origin g node rule).pending (old mode origin g node rule).fresh (old mode origin g node rule).mask
  have cursors:=cursors_before_code mode origin l t g node rule ctx
  have after:=ctx.resources.inputAfter
  rw [Listing8InputMask.Intact,Listing8LoopControl.memory mode origin l t g node rule ctx oldInput state image]
  dsimp only [Listing8LoopControl.failureEnd]
  rw [Listing8LoopInputBodyFrames.failure mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) oldInput b state image.body.state.head.graph.entry image.body.state.head.graph.forward input _ _
    extent.le (Or.inl (by omega)) (Or.inl (by omega))]
  exact Listing8MainInput.retained_image mode l t (values mode origin g node rule) oldInput b.state.head.input state image.body.state.head.graph.entry image.body.state.head.graph.forward input.state.head.input

end SmcTuring.Appendix.Listing8LoopControlReentryFields

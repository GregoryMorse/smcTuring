module
public import SmcTuring.Appendix.Listing8GlobalControlRegions
public import SmcTuring.Appendix.Listing8ControlTemplateBindings

public section
namespace SmcTuring.Appendix.Listing8GlobalControlBindings
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

/-- Both targets are obtained from the same reached original memory, without
assuming the selected branch or requiring an unchanged CALL displacement. -/
theorem original_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel limit : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (tail : Listing8FailLayout.Bounds mode origin l limit) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GlobalControlLayout.Current mode origin
      (Listing8GlobalJump.bodyEnd mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed).principal.memory := by
  have current:=Listing8ControlTemplateBindings.original_current mode origin l t v sentinel limit r owners copies boot body tail memory seed
  exact ⟨current.stackImage,current.prefixImage,RelativeCallTemplate.initial mode _ _ _ current.callImage,
    Listing8BeginReturn.target_current mode origin l t v sentinel r owners copies boot body (Listing8FailImage.backing mode origin memory) seed,
    Listing8FailImage.current mode origin l t v sentinel limit r owners copies boot body tail memory seed⟩

theorem original_jump (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel limit : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (tail : Listing8FailLayout.Bounds mode origin l limit) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8JumpReturn.program mode origin (Listing8GlobalJump.failed mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed))
      (Listing8GlobalJump.bodyEnd mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed) :=
  Listing8GlobalControlTemplates.all_decodes mode origin _ _
    (Listing8GlobalControlTemplates.initial mode origin _ (original_current mode origin l t v sentinel limit r owners copies boot body tail memory seed))
    (Listing8GlobalControlRegions.jump mode origin _ _
      (Listing8GlobalBoot.endpoint mode origin l t v sentinel r owners copies boot body
        (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin memory)) seed)
      (Listing8JumpImage.capacity mode origin l t sentinel boot body)
      (Listing8ControlTemplateBindings.original_current mode origin l t v sentinel limit r owners copies boot body tail memory seed))

theorem selected_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GlobalControlLayout.Current mode origin
      (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory := by
  have current:=Listing8ControlTemplateBindings.selected_current mode origin l t g node rule target ctx selected memory seed
  exact ⟨current.stackImage,current.prefixImage,RelativeCallTemplate.initial mode _ _ _ current.callImage,
    Listing8GraphNextStackImage.begin_packet mode origin l t g node rule target ctx selected memory seed,
    Listing8GraphNextFailImage.current mode origin l t g node rule target ctx selected memory seed⟩

theorem selected_jump (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8JumpReturn.program mode origin (Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed))
      (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed) :=
  Listing8GlobalControlTemplates.all_decodes mode origin _ _
    (Listing8GlobalControlTemplates.initial mode origin _ (selected_current mode origin l t g node rule target ctx selected memory seed))
    (Listing8GlobalControlRegions.jump mode origin _ _
      (Listing8GraphNextJump.entry mode origin l t g node rule target ctx selected memory seed)
      (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
      (Listing8ControlTemplateBindings.selected_current mode origin l t g node rule target ctx selected memory seed))

theorem maintained_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) (old : Listing8MainInput.OldInput)
    (state : StringExecution.State mode) (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Listing8GlobalControlLayout.Current mode origin
      (Listing8LoopControl.failureEnd mode origin l t g node rule state).principal.memory := by
  have current:=Listing8LoopControl.current mode origin l t g node rule ctx old state image
  exact ⟨current.stackImage,current.prefixImage,RelativeCallTemplate.initial mode _ _ _ current.callImage,
    Listing8LoopControlImage.begin_packet mode origin l t g node rule ctx old state image,
    Listing8LoopControlImage.fail_packet mode origin l t g node rule ctx old state image⟩

theorem maintained_jump (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) (old : Listing8MainInput.OldInput)
    (state : StringExecution.State mode) (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.failureEnd mode origin l t g node rule state) :=
  Listing8GlobalControlTemplates.all_decodes mode origin _ _
    (Listing8GlobalControlTemplates.initial mode origin _ (maintained_current mode origin l t g node rule ctx old state image))
    (Listing8GlobalControlRegions.jump mode origin _ _ (Listing8LoopControl.entry mode origin l t g node rule ctx old state image)
      (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
      (Listing8LoopControl.current mode origin l t g node rule ctx old state image))

end SmcTuring.Appendix.Listing8GlobalControlBindings

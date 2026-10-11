module
public import SmcTuring.Appendix.Listing8ControlExecutableTemplates
public import SmcTuring.Appendix.Listing8GraphNextFailReturn
public import SmcTuring.Appendix.Listing8LoopControl

public section
namespace SmcTuring.Appendix.Listing8ControlTemplateBindings
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem original_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel limit : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (tail : Listing8FailLayout.Bounds mode origin l limit) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8JumpReturn.Current mode origin
      (Listing8GlobalJump.failed mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed)
      (Listing8GlobalJump.bodyEnd mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed).principal.memory := by
  refine ⟨Listing8StackMetadata.stack_packet mode origin l t v sentinel r owners copies boot body
    (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin memory)) seed,
    Listing8JumpImage.current mode origin l t v sentinel r owners copies boot body (Listing8FailImage.backing mode origin memory) seed,
    Listing8GlobalJump.call_packet mode origin l t v sentinel r owners copies boot body (Listing8FailImage.backing mode origin memory) seed,?_⟩
  cases result : Listing8GlobalJump.failed mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed
  · exact Listing8BeginReturn.target_current mode origin l t v sentinel r owners copies boot body (Listing8FailImage.backing mode origin memory) seed
  · exact Listing8FailImage.current mode origin l t v sentinel limit r owners copies boot body tail memory seed

/-- Both actual original CALL outcomes share the proved whole-field store regions;
no branch outcome or future native packet is assumed. -/
theorem original (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel limit : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (tail : Listing8FailLayout.Bounds mode origin l limit) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Listing8ControlExecutableTemplates.Decodes mode origin
      (Listing8GlobalJump.failed mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed) reached.principal.memory)
      (Listing8JumpReturn.program mode origin (Listing8GlobalJump.failed mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed))
      (Listing8GlobalJump.bodyEnd mode origin l t v sentinel (Listing8FailImage.backing mode origin memory) seed) :=
  Listing8ControlExecutableTemplates.all_decodes mode origin _ _
    (Listing8GlobalBoot.endpoint mode origin l t v sentinel r owners copies boot body
      (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin memory)) seed)
    (Listing8JumpImage.capacity mode origin l t sentinel boot body)
    (original_current mode origin l t v sentinel limit r owners copies boot body tail memory seed)

theorem selected_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8JumpReturn.Current mode origin (Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed)
      (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory := by
  refine ⟨Listing8GraphNextStackImage.stack_packet mode origin l t g node rule target ctx selected memory seed,
    Listing8GraphNextStackImage.jump_prefix mode origin l t g node rule target ctx selected memory seed,
    Listing8GraphNextJump.call_packet mode origin l t g node rule target ctx selected memory seed,?_⟩
  cases result : Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed
  · exact Listing8GraphNextStackImage.begin_packet mode origin l t g node rule target ctx selected memory seed
  · exact Listing8GraphNextFailImage.current mode origin l t g node rule target ctx selected memory seed

theorem selected_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Listing8ControlExecutableTemplates.Decodes mode origin
      (Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed) reached.principal.memory)
      (Listing8JumpReturn.program mode origin (Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed))
      (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed) :=
  Listing8ControlExecutableTemplates.all_decodes mode origin _ _
    (Listing8GraphNextJump.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
    (selected_current mode origin l t g node rule target ctx selected memory seed)

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) (old : Listing8MainInput.OldInput)
    (state : StringExecution.State mode) (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8ControlExecutableTemplates.Decodes mode origin
      (Listing8LoopControl.failed mode origin l t g node rule state) reached.principal.memory)
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.failureEnd mode origin l t g node rule state) :=
  Listing8ControlExecutableTemplates.all_decodes mode origin _ _
    (Listing8LoopControl.entry mode origin l t g node rule ctx old state current)
    (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
    (Listing8LoopControl.current mode origin l t g node rule ctx old state current)

end SmcTuring.Appendix.Listing8ControlTemplateBindings

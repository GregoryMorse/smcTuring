module
public import SmcTuring.Appendix.Listing8FailureExecutableTemplates
public import SmcTuring.Appendix.Listing8GraphNextCallImage
public import SmcTuring.Appendix.Listing8LoopControlImage

public section
namespace SmcTuring.Appendix.Listing8FailureTemplateBindings
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

/-- The actual halt-node declaration is after the complete phase and CALL;
the initializer's transient indirect stores therefore stay outside both. -/
theorem sentinel_after (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing8FailureLayout.callPC mode
      (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5≤
        nodePC mode origin g g.halt := by
  have lower:=Listing8GraphLayout.node_lower mode origin g.transitions g.halt.val
  change Listing8GraphLayout.input mode origin g.transitions≤nodePC mode origin g g.halt at lower
  simp only [Listing8GraphLayout.input,Listing8GraphLayout.reset,Listing8GraphLayout.transition,Listing8FullTableImage.start] at lower
  rw [Listing8FailLayout.end_offset] at lower
  have position:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode
    (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=
      Listing8JumpLayout.callPC mode origin at position
  rw [position,(Listing8JumpLayout.positions mode origin).1]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at lower ⊢ <;> omega

theorem original (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8FailureGeometry.Bounds mode l t sentinel begin)
    (sentinelOutside : sentinel+mode.wordBytes≤(Listing8FailureGeometry.region mode l sentinel begin).start ∨
      Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+5≤sentinel)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Listing8FailureExecutableTemplates.Decodes mode
      (Listing8FailureGeometry.region mode l sentinel begin) reached.principal.memory)
      ((Listing8FailureTrace.program mode (Listing8FailureGeometry.region mode l sentinel begin)
        (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed)).map StringStack.Form.previous)
      (Listing8GlobalFailure.entryState mode l t v sentinel begin extra seed) :=
  Listing8FailureExecutableTemplates.all_decodes mode _ (Listing8FailureGeometry.local_bounds mode l t sentinel begin r bounds)
    sentinelOutside _ (Listing8GlobalFailure.entry mode l t v sentinel begin r owners copies bounds extra seed)
    (Listing8FailureReuseImage.from_initial mode _ _ (Listing8FailureGlobalImage.current_region mode l t v sentinel begin r owners copies bounds extra seed))
    (RelativeCallTemplate.initial mode _ _ _ (Listing8FailureGlobalImage.current_call mode l t v sentinel begin r owners copies bounds extra seed))

theorem selected_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Listing8FailureExecutableTemplates.Decodes mode
      (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) reached.principal.memory)
      ((Listing8FailureTrace.program mode
        (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
        (Listing8GraphNextState.finish mode origin l t g node rule target memory seed)).map StringStack.Form.previous)
      (Listing8GraphNextState.finish mode origin l t g node rule target memory seed) :=
  Listing8FailureExecutableTemplates.all_decodes mode _ (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body)
    (Or.inr (sentinel_after mode origin l t g node rule ctx)) _
    (Listing8GraphNextState.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextFailureImage.current mode origin l t g node rule target ctx selected memory seed)
    (RelativeCallTemplate.initial mode _ _ _ (Listing8GraphNextCallImage.entry_packet mode origin l t g node rule target ctx selected memory seed))

theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) (old : Listing8MainInput.OldInput)
    (state : StringExecution.State mode) (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8FailureExecutableTemplates.Decodes mode
      (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) reached.principal.memory)
      ((Listing8FailureTrace.program mode
        (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
        (Listing8LoopState.finish mode l t (values mode origin g node rule) state)).map StringStack.Form.previous)
      (Listing8LoopState.finish mode l t (values mode origin g node rule) state) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have entry:=current.body.state.head.graph.entry
  have forward:=current.body.state.head.graph.forward
  have position:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode
    (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=
      Listing8JumpLayout.callPC mode origin at position
  have original : ByteMemory.bytesAt state.principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) 5=
      Native.encode mode (.callRelative (Listing8FailureLayout.original mode
        (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))) := by
    rw [Listing8FailureLayout.original,position]
    exact current.callImage
  exact Listing8FailureExecutableTemplates.all_decodes mode _ (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body)
    (Or.inr (sentinel_after mode origin l t g node rule ctx)) _
    (Listing8LoopState.endpoint mode l t _ old b.state state entry forward image.state)
    (Listing8LoopFailurePrefix.current_after_state mode l t _ old _ _ b state entry forward image)
    (RelativeCallTemplate.initial mode _ _ _ (Listing8LoopCallImage.entry_packet mode l t _ _ _ old b state entry forward image original))

end SmcTuring.Appendix.Listing8FailureTemplateBindings

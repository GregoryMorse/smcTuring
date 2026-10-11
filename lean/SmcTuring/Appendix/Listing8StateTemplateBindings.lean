module
public import SmcTuring.Appendix.Listing8StateExecutableTemplates
public import SmcTuring.Appendix.Listing8GraphNextState
public import SmcTuring.Appendix.Listing8GlobalState
public import SmcTuring.Appendix.Listing8LoopState

public section
namespace SmcTuring.Appendix.Listing8StateTemplateBindings
open Native Listing8CopyImage Listing8StateGeometry
abbrev Targets := Listing8PointerCopies.Targets

theorem original (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8StateTemplateFields.arithmetic mode (region mode l),
        DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ descriptor∈Listing8StateTemplateFields.fixed mode (region mode l),
        MixedFixedTemplates.Decodes mode descriptor reached.principal.memory))
      ((Listing8StateTrace.program mode (region mode l) (Listing8GlobalState.entryState mode l t v extra seed)).map
        (StringStoreWrites.liftDword mode)) (Listing8GlobalState.entryState mode l t v extra seed) :=
  Listing8StateExecutableTemplates.all_decodes mode (region mode l) (local_bounds mode l t r bounds) _
    (Listing8GlobalState.entry mode l t v r owners copies bounds extra seed)
    (Listing8StateImage.helper_current mode l t v r owners copies bounds extra seed)
    (Listing8StateImage.headers_current mode l t v r owners copies bounds extra seed)

theorem selected_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Listing8SourceGraph.Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8StateTemplateFields.arithmetic mode (region mode l),
        DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ descriptor∈Listing8StateTemplateFields.fixed mode (region mode l),
        MixedFixedTemplates.Decodes mode descriptor reached.principal.memory))
      ((Listing8StateTrace.program mode (region mode l)
        (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed) :=
  Listing8StateExecutableTemplates.all_decodes mode (region mode l) (local_bounds mode l t ctx.resources ctx.body.state) _
    (Listing8GraphNextHead.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextStateImage.helper_current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextStateImage.headers_current mode origin l t g node rule target ctx selected memory seed)

theorem maintained (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (old : Listing8MainInput.OldInput) (b : Listing8LoopState.Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8LoopState.Current mode l t v old state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8StateTemplateFields.arithmetic mode (region mode l),
        DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ descriptor∈Listing8StateTemplateFields.fixed mode (region mode l),
        MixedFixedTemplates.Decodes mode descriptor reached.principal.memory))
      ((Listing8StateTrace.program mode (region mode l) (Listing8LoopHead.finish mode l t v state)).map
        (StringStoreWrites.liftDword mode)) (Listing8LoopHead.finish mode l t v state) :=
  Listing8StateExecutableTemplates.all_decodes mode (region mode l)
    (local_bounds mode l t b.head.input.input.prefixBounds.resources b.state) _
    (Listing8LoopHead.endpoint mode l t v old b.head state entry forward current.head)
    (Listing8LoopStatePrefix.current_after_head mode l t v old b state entry forward current).helpers
    (Listing8LoopStatePrefix.current_after_head mode l t v old b state entry forward current).headers

end SmcTuring.Appendix.Listing8StateTemplateBindings

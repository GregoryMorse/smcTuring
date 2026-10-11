module
public import SmcTuring.Appendix.Listing8HeadExecutableTemplates
public import SmcTuring.Appendix.Listing8GraphNextHead
public import SmcTuring.Appendix.Listing8LoopHead

public section
namespace SmcTuring.Appendix.Listing8HeadTemplateBindings
open Native Listing8CopyImage Listing8DirectionGeometry
abbrev Targets := Listing8PointerCopies.Targets

theorem original (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8HeadTemplateFields.arithmetic mode (region mode l),
        DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ helper∈Listing8HeadTailBounds.xorLayouts mode (region mode l),
        DwordXorTemplates.Decodes mode helper reached.principal.memory))
      ((Listing8HeadTailTrace.program mode (region mode l) (Listing8GlobalHead.entryState mode l t v extra seed)).map
        (StringStoreWrites.liftDword mode)) (Listing8GlobalHead.entryState mode l t v extra seed) :=
  Listing8HeadExecutableTemplates.all_decodes mode (region mode l) (Listing8HeadGeometry.tail_bounds mode l t bounds) _
    (Listing8GlobalHead.entry mode l t v r owners copies bounds extra seed)
    (Listing8HeadImage.xor_current mode l t v r owners copies bounds extra seed)
    (Listing8HeadImage.headers_current mode l t v r owners copies bounds extra seed)

theorem selected_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Listing8SourceGraph.Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8HeadTemplateFields.arithmetic mode (region mode l),
        DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ helper∈Listing8HeadTailBounds.xorLayouts mode (region mode l),
        DwordXorTemplates.Decodes mode helper reached.principal.memory))
      ((Listing8HeadTailTrace.program mode (region mode l)
        (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed) :=
  Listing8HeadExecutableTemplates.all_decodes mode (region mode l) (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) _
    (Listing8GraphNextDirection.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextHead.xor_current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextHead.tail_current mode origin l t g node rule target ctx selected memory seed)

theorem maintained (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (old : Listing8MainInput.OldInput) (b : Listing8LoopHead.Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8LoopHead.Current mode l t v old state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8HeadTemplateFields.arithmetic mode (region mode l),
        DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ helper∈Listing8HeadTailBounds.xorLayouts mode (region mode l),
        DwordXorTemplates.Decodes mode helper reached.principal.memory))
      ((Listing8HeadTailTrace.program mode (region mode l) (Listing8LoopDirection.finish mode l t v state)).map
        (StringStoreWrites.liftDword mode)) (Listing8LoopDirection.finish mode l t v state) :=
  Listing8HeadExecutableTemplates.all_decodes mode (region mode l) (Listing8HeadGeometry.tail_bounds mode l t b.direction) _
    (Listing8LoopDirection.endpoint mode l t v old b state entry forward current)
    (Listing8LoopDirection.current_after mode l t v old b state entry forward current).xorImage
    (Listing8LoopDirection.current_after mode l t v old b state entry forward current).tailHeaders

end SmcTuring.Appendix.Listing8HeadTemplateBindings

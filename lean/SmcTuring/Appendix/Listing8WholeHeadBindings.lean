module
public import SmcTuring.Appendix.Listing8WholeHeadTemplates
public import SmcTuring.Appendix.Listing8HeadTemplateBindings
public import SmcTuring.Appendix.Listing8DirectionBodyFrames

public section
namespace SmcTuring.Appendix.Listing8WholeHeadBindings
open Native Listing8CopyImage Listing8DirectionGeometry
abbrev Targets := Listing8PointerCopies.Targets

theorem current (mode : Mode) (layout : Listing8DirectionLayout.Layout)
    (bounds : Listing8HeadTailBounds.Bounds mode layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (image : Listing8LoopDirectionImage.Current mode layout state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8DirectionTemplateFields.templates mode layout,DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ descriptor∈Listing8DirectionTemplateFields.fixed mode layout,MixedFixedTemplates.Decodes mode descriptor reached.principal.memory) ∧
      (∀ helper∈Listing8HeadTailBounds.xorLayouts mode layout,DwordXorTemplates.Decodes mode helper reached.principal.memory))
      ((Listing8WholeHeadTemplates.program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
  apply Listing8WholeHeadTemplates.all_decodes mode layout bounds state entry image.helpers _ image.xorImage
  intro site member
  simp only [Listing8DirectionTemplateFields.sites,List.mem_append] at member
  rcases member with (a | b) | c
  · exact image.arithmetic site a
  · exact image.tailHeaders site (List.mem_append_left _ b)
  · exact image.tailHeaders site (List.mem_append_right _ c)

theorem original_xor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory
      (Listing8DirectionLayout.selectionEnd mode (region mode l))
      (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (region mode l))).length=
      DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (region mode l)) := by
  have member : (Listing8DirectionLayout.selectionEnd mode (region mode l),
      (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (region mode l))).length)∈
      Listing8DirectionWindows.windows mode (region mode l) := by
    simp [Listing8DirectionWindows.windows,Listing8DirectionWindows.xor_size]
  rw [←Listing8DirectionBodyFrames.direction mode l t v r owners copies bounds extra seed _ member]
  exact Listing8HeadImage.xor_current mode l t v r owners copies bounds extra seed

theorem original_tail (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordPackets.Intact mode (Listing8DirectionLayout.masks mode (region mode l)++Listing8DirectionLayout.heads mode (region mode l))
      (Listing8GlobalDirection.entryState mode l t v extra seed).principal.memory := by
  intro reader readerMember
  have member : (reader.pc,6)∈Listing8DirectionWindows.windows mode (region mode l) := by
    simp only [Listing8DirectionWindows.windows,List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨reader,readerMember,rfl⟩)
  rw [DwordPackets.Current,←Listing8DirectionBodyFrames.direction mode l t v r owners copies bounds extra seed _ member]
  exact Listing8HeadImage.headers_current mode l t v r owners copies bounds extra seed reader readerMember

theorem original (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8DirectionTemplateFields.templates mode (region mode l),DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ descriptor∈Listing8DirectionTemplateFields.fixed mode (region mode l),MixedFixedTemplates.Decodes mode descriptor reached.principal.memory) ∧
      (∀ helper∈Listing8HeadTailBounds.xorLayouts mode (region mode l),DwordXorTemplates.Decodes mode helper reached.principal.memory))
      ((Listing8WholeHeadTemplates.program mode (region mode l) (Listing8GlobalDirection.entryState mode l t v extra seed)).map
        (StringStoreWrites.liftDword mode)) (Listing8GlobalDirection.entryState mode l t v extra seed) :=
  current mode (region mode l) (Listing8HeadGeometry.tail_bounds mode l t bounds) _
    (Listing8GlobalDirection.entry mode l t v r owners copies bounds extra seed)
    ⟨Listing8GlobalDirection.helper_current mode l t v r owners copies bounds extra seed,
      Listing8GlobalDirection.arithmetic_current mode l t v r owners copies bounds extra seed,
      original_xor mode l t v r owners copies bounds extra seed,original_tail mode l t v r owners copies bounds extra seed⟩

theorem selected_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Listing8SourceGraph.Graph) (node : Fin g.nodes) (rule target : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8DirectionTemplateFields.templates mode (region mode l),DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ descriptor∈Listing8DirectionTemplateFields.fixed mode (region mode l),MixedFixedTemplates.Decodes mode descriptor reached.principal.memory) ∧
      (∀ helper∈Listing8HeadTailBounds.xorLayouts mode (region mode l),DwordXorTemplates.Decodes mode helper reached.principal.memory))
      ((Listing8WholeHeadTemplates.program mode (region mode l)
        (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed) :=
  current mode (region mode l) (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) _
    (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed)
    ⟨Listing8GraphNextDirectionImage.helper_current mode origin l t g node rule target ctx selected memory seed,
      Listing8GraphNextDirectionImage.arithmetic_current mode origin l t g node rule target ctx selected memory seed,
      Listing8GraphNextDirectionImage.xor_current mode origin l t g node rule target ctx selected memory seed,
      Listing8GraphNextDirectionImage.tail_current mode origin l t g node rule target ctx selected memory seed⟩

theorem maintained (mode : Mode) (l : Layout) (t : Targets) (v : Values mode)
    (old : Listing8MainInput.OldInput) (b : Listing8LoopDirection.Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (image : Listing8LoopDirection.Current mode l t v old state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8DirectionTemplateFields.templates mode (region mode l),DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ descriptor∈Listing8DirectionTemplateFields.fixed mode (region mode l),MixedFixedTemplates.Decodes mode descriptor reached.principal.memory) ∧
      (∀ helper∈Listing8HeadTailBounds.xorLayouts mode (region mode l),DwordXorTemplates.Decodes mode helper reached.principal.memory))
      ((Listing8WholeHeadTemplates.program mode (region mode l) (Listing8MainInput.finish mode l t v state)).map
        (StringStoreWrites.liftDword mode)) (Listing8MainInput.finish mode l t v state) :=
  current mode (region mode l) (Listing8HeadGeometry.tail_bounds mode l t b.direction) _
    (Listing8MainInput.endpoint mode l t v old b.input state entry forward image.input)
    (Listing8LoopDirectionPrefix.current_after_input mode l t v old b state entry forward image)

end SmcTuring.Appendix.Listing8WholeHeadBindings

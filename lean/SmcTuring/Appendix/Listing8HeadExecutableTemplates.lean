module
public import SmcTuring.Appendix.Listing8HeadTemplateFields
public import SmcTuring.Native.MixedTemplateGeometry

public section
namespace SmcTuring.Appendix.Listing8HeadExecutableTemplates
open Native Listing8DirectionLayout Listing8HeadTailBounds Listing8HeadTemplateFields

@[expose] def Property (mode : Mode) (layout : Layout) (state : StringExecution.State mode) : Prop :=
  DwordTemplateCollection.All (Listing8HeadTemplateFields.arithmetic mode layout) state.principal.memory ∧
    DwordXorSequence.Intact mode (xorLayouts mode layout) state.principal.memory

theorem descriptor_count (mode : Mode) (layout : Layout) :
    (Listing8HeadTemplateFields.arithmetic mode layout).length+3*(xorLayouts mode layout).length=if mode=.x86 then 5 else 10 := by
  cases mode <;> simp [Listing8HeadTemplateFields.arithmetic,Listing8HeadTemplateFields.sites,masks,heads,group,xorLayouts]

theorem regions (mode : Mode) (layout : Layout) (bounds : Bounds mode layout)
    (owns : Nat → Nat → Prop) (fields : ∀ address,Allowed mode layout address → owns address 4)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (selectionEnd mode layout)) :
    StringStoreRegions.Run mode owns ((Listing8HeadTailTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
  have helpersOwned := helper_fields mode layout bounds
  have packetsOwned := packet_fields mode layout bounds
  have first := DwordXorRegionRuns.sequence mode owns (xorLayouts mode layout) (selectionEnd mode layout)
    (xor_chain mode layout) (xor_valid mode layout bounds)
    (fun helper member => ⟨fields _ (helpersOwned helper member).1,fields _ (helpersOwned helper member).2⟩) state entry
  have second := DwordXorRegionRuns.packets mode owns (masks mode layout) (maskPC mode layout)
    (masks_chain mode layout) (fun site member => packets_valid mode layout bounds site (List.mem_append_left _ member))
    (fun site member => fields _ (packetsOwned site (List.mem_append_left _ member)))
    (Listing8HeadTailTrace.xorFinish mode layout state) (Listing8HeadTailTrace.xor_endpoint mode layout bounds state entry)
  have third := DwordXorRegionRuns.packets mode owns (heads mode layout) (directionPC mode layout)
    (heads_chain mode layout) (fun site member => packets_valid mode layout bounds site (List.mem_append_right _ member))
    (fun site member => fields _ (packetsOwned site (List.mem_append_right _ member)))
    (Listing8HeadTailTrace.maskFinish mode layout state) (Listing8HeadTailTrace.mask_endpoint mode layout bounds state entry)
  rw [Listing8HeadTailTrace.program,List.map_append,List.map_append,StringStoreRegions.append,
    StringStoreRegions.append,StringWrites.run_append,DwordXorWrites.sequence_run]
  unfold Listing8HeadTailTrace.xorFinish
  rw [DwordPacketWrites.run]
  simpa only [Listing8HeadTailTrace.maskFinish,Listing8HeadTailTrace.xorFinish] using And.intro (And.intro first second) third

theorem initial (mode : Mode) (layout : Layout) (state : StringExecution.State mode)
    (xorImage : ByteMemory.bytesAt state.principal.memory (selectionEnd mode layout)
      (DwordXorSequence.bytes mode (xorLayouts mode layout)).length=DwordXorSequence.bytes mode (xorLayouts mode layout))
    (headers : DwordPackets.Intact mode (Listing8HeadTemplateFields.sites mode layout) state.principal.memory) : Property mode layout state :=
  ⟨DwordPacketTemplateRuns.initial mode _ _ headers,
    DwordXorSequence.initial_helpers mode _ _ (xor_chain mode layout) _ xorImage⟩

/-- Both mask/head operand descriptors and every fixed XOR helper are
valid together during the complete actual head-tail execution. -/
theorem all_states (mode : Mode) (layout : Layout) (bounds : Bounds mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (selectionEnd mode layout))
    (xorImage : ByteMemory.bytesAt state.principal.memory (selectionEnd mode layout)
      (DwordXorSequence.bytes mode (xorLayouts mode layout)).length=DwordXorSequence.bytes mode (xorLayouts mode layout))
    (headers : DwordPackets.Intact mode (Listing8HeadTemplateFields.sites mode layout) state.principal.memory) :
    StringTemplateStates.Run mode (Property mode layout)
      ((Listing8HeadTailTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
  have intact := initial mode layout state xorImage headers
  exact MixedTemplateGeometry.conjunction mode _ _ _ state
    (StringStoreRegions.arithmetic_states mode (Listing8HeadTemplateFields.arithmetic mode layout) _ state intact.1
      (regions mode layout bounds _ (fun address allowed => compatible mode layout address allowed) state entry))
    (DwordXorTemplates.all_states mode (xorLayouts mode layout) _ state intact.2
      (regions mode layout bounds _ (fun address allowed => frames mode layout address allowed) state entry))

theorem all_decodes (mode : Mode) (layout : Layout) (bounds : Bounds mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (selectionEnd mode layout))
    (xorImage : ByteMemory.bytesAt state.principal.memory (selectionEnd mode layout)
      (DwordXorSequence.bytes mode (xorLayouts mode layout)).length=DwordXorSequence.bytes mode (xorLayouts mode layout))
    (headers : DwordPackets.Intact mode (Listing8HeadTemplateFields.sites mode layout) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8HeadTemplateFields.arithmetic mode layout,DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ helper∈xorLayouts mode layout,DwordXorTemplates.Decodes mode helper reached.principal.memory))
      ((Listing8HeadTailTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun reached both => ⟨fun descriptor member => DwordTemplateCollection.decodes mode descriptor _ (both.1 descriptor member),
      fun helper member => DwordXorTemplates.decodes mode helper reached.principal.memory (both.2 helper member)⟩)
    (all_states mode layout bounds state entry xorImage headers)

end SmcTuring.Appendix.Listing8HeadExecutableTemplates

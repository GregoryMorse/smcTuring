module
public import SmcTuring.Appendix.Listing8DirectionTemplateFields
public import SmcTuring.Native.StringDwordRuns

public section
namespace SmcTuring.Appendix.Listing8WholeHeadTemplates
open Native Listing8DirectionLayout Listing8HeadTailBounds

@[expose] def program (mode : Mode) (layout : Layout) (state : StringExecution.State mode) :=
  Listing8DirectionTrace.program mode layout state++
    Listing8HeadTailTrace.program mode layout (Listing8DirectionTrace.finish mode layout state)
@[expose] def Property (mode : Mode) (layout : Layout) (state : StringExecution.State mode) : Prop :=
  DwordTemplateCollection.All (Listing8DirectionTemplateFields.templates mode layout) state.principal.memory ∧
    MixedFixedTemplates.All mode (Listing8DirectionTemplateFields.fixed mode layout) state.principal.memory ∧
    DwordXorSequence.Intact mode (xorLayouts mode layout) state.principal.memory

theorem descriptor_count (mode : Mode) (layout : Layout) :
    (Listing8DirectionTemplateFields.templates mode layout).length+
      (Listing8DirectionTemplateFields.fixed mode layout).length+3*(xorLayouts mode layout).length=
      if mode=.x86 then 12 else 27 := by
  cases mode <;> simp [Listing8DirectionTemplateFields.templates,Listing8DirectionTemplateFields.sites,
    Listing8DirectionTemplateFields.fixed,arithmetic,masks,heads,group,helpers,duplicate,copy,xorLayouts,MixedFixedTemplates.copyEntries]

theorem regions (mode : Mode) (layout : Layout) (bounds : Bounds mode layout)
    (owns : Nat → Nat → Prop)
    (fields : ∀ address,Listing8DirectionTemplateFields.Allowed mode layout address → owns address 4)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start) :
    StringStoreRegions.Run mode owns ((program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
  have helpersOwned := Listing8DirectionTemplateFields.helper_fields mode layout
  have packetsOwned := Listing8DirectionTemplateFields.packet_fields mode layout bounds
  have first := StringStoreRegions.mixed mode owns _ state
    (MixedFieldOwnership.sequence mode (helpers mode layout) layout.start (helper_chain mode layout)
      (Listing8DirectionBounds.helper_valid mode layout bounds.capacity) owns
      (fun helper member => ⟨fields _ (helpersOwned helper member).1,fields _ (helpersOwned helper member).2⟩)
      state.principal entry)
  rw [MixedSequenceTemplateRuns.forms] at first
  have second := DwordXorRegionRuns.packets mode owns (arithmetic mode layout) (backPC mode layout)
    (arithmetic_chain mode layout) (Listing8DirectionBounds.arithmetic_valid mode layout bounds.capacity)
    (fun site member => fields _ (packetsOwned site (by simp only [Listing8DirectionTemplateFields.sites,List.mem_append];exact Or.inl (Or.inl member))))
    (Listing8DirectionTrace.helperFinish mode layout state) (Listing8DirectionTrace.helper_endpoint mode layout bounds.capacity state entry)
  have third := Listing8HeadExecutableTemplates.regions mode layout bounds owns
    (by
      intro address allowed
      rcases allowed with before | rfl | ⟨long,rfl⟩
      · exact fields address (Or.inl before)
      · exact fields _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact fields _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨long,rfl⟩)))))
    (Listing8DirectionTrace.finish mode layout state)
    (Listing8DirectionTrace.endpoint mode layout bounds.capacity state entry)
  have direction : StringStoreRegions.Run mode owns
      ((Listing8DirectionTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
    rw [Listing8DirectionTrace.program,List.map_append,StringStoreRegions.append,StringDwordRuns.run]
    exact ⟨first,second⟩
  have directionRun : StringWrites.run mode
      ((Listing8DirectionTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state=
      Listing8DirectionTrace.finish mode layout state := by
    rw [Listing8DirectionTrace.program,List.map_append,StringWrites.run_append,StringDwordRuns.run]
    unfold Listing8DirectionTrace.helperFinish
    rw [DwordPacketWrites.run]
    rfl
  rw [program,List.map_append,StringStoreRegions.append,directionRun]
  exact ⟨direction,third⟩

theorem initial (mode : Mode) (layout : Layout) (state : StringExecution.State mode)
    (helperImage : ByteMemory.bytesAt state.principal.memory layout.start
      (DwordMixedSequence.bytes mode (helpers mode layout)).length=DwordMixedSequence.bytes mode (helpers mode layout))
    (headers : DwordPackets.Intact mode (Listing8DirectionTemplateFields.sites mode layout) state.principal.memory)
    (xorImage : ByteMemory.bytesAt state.principal.memory (selectionEnd mode layout)
      (DwordXorSequence.bytes mode (xorLayouts mode layout)).length=DwordXorSequence.bytes mode (xorLayouts mode layout)) :
    Property mode layout state := by
  refine ⟨DwordPacketTemplateRuns.initial mode _ _ headers,?_,
    DwordXorSequence.initial_helpers mode _ _ (xor_chain mode layout) _ xorImage⟩
  have original := DwordMixedSequence.intact_of_bytes mode (helpers mode layout) layout.start (helper_chain mode layout)
    state.principal.memory helperImage
  intro descriptor member
  rcases List.mem_flatMap.mp member with ⟨helper,inside,packet⟩
  exact MixedFixedTemplates.copy_initial mode helper state.principal.memory (original helper inside) descriptor packet

theorem all_states (mode : Mode) (layout : Layout) (bounds : Bounds mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (helperImage : ByteMemory.bytesAt state.principal.memory layout.start
      (DwordMixedSequence.bytes mode (helpers mode layout)).length=DwordMixedSequence.bytes mode (helpers mode layout))
    (headers : DwordPackets.Intact mode (Listing8DirectionTemplateFields.sites mode layout) state.principal.memory)
    (xorImage : ByteMemory.bytesAt state.principal.memory (selectionEnd mode layout)
      (DwordXorSequence.bytes mode (xorLayouts mode layout)).length=DwordXorSequence.bytes mode (xorLayouts mode layout)) :
    StringTemplateStates.Run mode (Property mode layout) ((program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
  have intact := initial mode layout state helperImage headers xorImage
  have a := StringStoreRegions.arithmetic_states mode (Listing8DirectionTemplateFields.templates mode layout) _ state intact.1
    (regions mode layout bounds _ (fun address allowed => Listing8DirectionTemplateFields.compatible mode layout address allowed) state entry)
  have fixedRun := StringStoreRegions.fixed_states mode (Listing8DirectionTemplateFields.fixed mode layout) _ state intact.2.1
    (regions mode layout bounds _ (fun address allowed => Listing8DirectionTemplateFields.fixed_frames mode layout address allowed) state entry)
  have c := DwordXorTemplates.all_states mode (xorLayouts mode layout) _ state intact.2.2
    (regions mode layout bounds _ (fun address allowed => Listing8DirectionTemplateFields.xor_frames mode layout address allowed) state entry)
  exact MixedTemplateGeometry.conjunction mode _ _ _ state a
    (MixedTemplateGeometry.conjunction mode _ _ _ state fixedRun c)

theorem all_decodes (mode : Mode) (layout : Layout) (bounds : Bounds mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (helperImage : ByteMemory.bytesAt state.principal.memory layout.start
      (DwordMixedSequence.bytes mode (helpers mode layout)).length=DwordMixedSequence.bytes mode (helpers mode layout))
    (headers : DwordPackets.Intact mode (Listing8DirectionTemplateFields.sites mode layout) state.principal.memory)
    (xorImage : ByteMemory.bytesAt state.principal.memory (selectionEnd mode layout)
      (DwordXorSequence.bytes mode (xorLayouts mode layout)).length=DwordXorSequence.bytes mode (xorLayouts mode layout)) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈Listing8DirectionTemplateFields.templates mode layout,
        DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ descriptor∈Listing8DirectionTemplateFields.fixed mode layout,
        MixedFixedTemplates.Decodes mode descriptor reached.principal.memory) ∧
      (∀ helper∈xorLayouts mode layout,DwordXorTemplates.Decodes mode helper reached.principal.memory))
      ((program mode layout state).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun reached all => ⟨fun descriptor member => DwordTemplateCollection.decodes mode descriptor _ (all.1 descriptor member),
      fun descriptor member => MixedFixedTemplates.decodes mode descriptor _ (all.2.1 descriptor member),
      fun helper member => DwordXorTemplates.decodes mode helper reached.principal.memory (all.2.2 helper member)⟩)
    (all_states mode layout bounds state entry helperImage headers xorImage)

theorem at_prefix (mode : Mode) (layout : Layout) (bounds : Bounds mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (helperImage : ByteMemory.bytesAt state.principal.memory layout.start
      (DwordMixedSequence.bytes mode (helpers mode layout)).length=DwordMixedSequence.bytes mode (helpers mode layout))
    (headers : DwordPackets.Intact mode (Listing8DirectionTemplateFields.sites mode layout) state.principal.memory)
    (xorImage : ByteMemory.bytesAt state.principal.memory (selectionEnd mode layout)
      (DwordXorSequence.bytes mode (xorLayouts mode layout)).length=DwordXorSequence.bytes mode (xorLayouts mode layout))
    (before after : List (StringStack.Form mode))
    (cut : (program mode layout state).map (StringStoreWrites.liftDword mode)=before++after) :
    (∀ descriptor∈Listing8DirectionTemplateFields.templates mode layout,
      DwordTemplateCollection.Decodes mode descriptor (StringWrites.run mode before state).principal.memory) ∧
    (∀ descriptor∈Listing8DirectionTemplateFields.fixed mode layout,
      MixedFixedTemplates.Decodes mode descriptor (StringWrites.run mode before state).principal.memory) ∧
    (∀ helper∈xorLayouts mode layout,DwordXorTemplates.Decodes mode helper (StringWrites.run mode before state).principal.memory) := by
  have actual := all_decodes mode layout bounds state entry helperImage headers xorImage
  rw [cut] at actual
  exact StringTemplateStates.at_prefix mode _ before after state actual

end SmcTuring.Appendix.Listing8WholeHeadTemplates

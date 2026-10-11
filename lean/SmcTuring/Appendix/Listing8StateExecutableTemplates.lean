module
public import SmcTuring.Appendix.Listing8StateTemplateFields
public import SmcTuring.Native.MixedTemplateGeometry
public import SmcTuring.Native.StringDwordRuns

public section
namespace SmcTuring.Appendix.Listing8StateExecutableTemplates
open Native Listing8StateLayout Listing8StateTemplateFields

@[expose] def Property (mode : Mode) (layout : Layout) (state : StringExecution.State mode) : Prop :=
  DwordTemplateCollection.All (arithmetic mode layout) state.principal.memory ∧
    MixedFixedTemplates.All mode (fixed mode layout) state.principal.memory

theorem descriptor_count (mode : Mode) (layout : Layout) :
    (arithmetic mode layout).length+(fixed mode layout).length=if mode=.x86 then 6 else 12 := by
  cases mode <;> simp [arithmetic,fixed,packets,newPackets,masks,updates,Listing8DirectionLayout.group,
    helpers,Listing8PointerCopies.split,MixedFixedTemplates.copyEntries]

theorem initial (mode : Mode) (layout : Layout) (state : StringExecution.State mode)
    (helperImage : ByteMemory.bytesAt state.principal.memory layout.start (DwordMixedSequence.bytes mode (helpers mode layout)).length=
      DwordMixedSequence.bytes mode (helpers mode layout))
    (headers : DwordPackets.Intact mode (packets mode layout) state.principal.memory) : Property mode layout state := by
  refine ⟨DwordPacketTemplateRuns.initial mode _ _ headers,?_⟩
  have original := DwordMixedSequence.intact_of_bytes mode (helpers mode layout) layout.start (helper_chain mode layout)
    state.principal.memory helperImage
  intro descriptor member
  rcases List.mem_flatMap.mp member with ⟨helper,inside,packet⟩
  exact MixedFixedTemplates.copy_initial mode helper state.principal.memory (original helper inside) descriptor packet

/-- All helper and arithmetic descriptors survive jointly throughout the
whole actual state-selection phase. Only original bytes and static bounds
are supplied; every subsequent PC and complete write window is derived. -/
theorem all_states (mode : Mode) (layout : Layout) (bounds : Listing8StateBounds.Bounds mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (helperImage : ByteMemory.bytesAt state.principal.memory layout.start (DwordMixedSequence.bytes mode (helpers mode layout)).length=
      DwordMixedSequence.bytes mode (helpers mode layout))
    (headers : DwordPackets.Intact mode (packets mode layout) state.principal.memory) :
    StringTemplateStates.Run mode (Property mode layout)
      ((Listing8StateTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state := by
  have intact := initial mode layout state helperImage headers
  have helpersOwned := helper_fields mode layout bounds
  have packetsOwned := packet_fields mode layout bounds
  have first := MixedTemplateGeometry.conjunction mode _ _ _ state
    (MixedSequenceTemplateRuns.all_states mode (arithmetic mode layout) (helpers mode layout) layout.start
      (helper_chain mode layout) (Listing8StateBounds.helper_valid mode layout bounds)
      (fun helper member => ⟨compatible mode layout _ (helpersOwned helper member).1,
        compatible mode layout _ (helpersOwned helper member).2⟩) state entry intact.1)
    (MixedSequenceTemplateRuns.fixed_states mode (fixed mode layout) (helpers mode layout) layout.start
      (helper_chain mode layout) (Listing8StateBounds.helper_valid mode layout bounds)
      (fun helper member => ⟨frames mode layout _ (helpersOwned helper member).1,
        frames mode layout _ (helpersOwned helper member).2⟩) state entry intact.2)
  have atEnd := StringTemplateStates.at_prefix mode _ _ [] state (by simpa only [List.append_nil] using first)
  rw [StringDwordRuns.run] at atEnd
  have later := Listing8StateTrace.helper_endpoint mode layout bounds state entry
  have second := MixedTemplateGeometry.conjunction mode _ _ _ (Listing8StateTrace.helperFinish mode layout state)
    (DwordPacketTemplateRuns.all_states mode (arithmetic mode layout) (packets mode layout) (newPC mode layout)
      (packet_chain mode layout) (Listing8StateBounds.packet_valid mode layout bounds)
      (fun site member => compatible mode layout _ (packetsOwned site member)) _ later atEnd.1)
    (DwordPacketTemplateRuns.fixed_states mode (fixed mode layout) (packets mode layout) (newPC mode layout)
      (packet_chain mode layout) (Listing8StateBounds.packet_valid mode layout bounds)
      (fun site member => frames mode layout _ (packetsOwned site member)) _ later atEnd.2)
  rw [Listing8StateTrace.program,List.map_append,StringTemplateStates.append,StringDwordRuns.run]
  exact ⟨first,second⟩

theorem all_decodes (mode : Mode) (layout : Layout) (bounds : Listing8StateBounds.Bounds mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (helperImage : ByteMemory.bytesAt state.principal.memory layout.start (DwordMixedSequence.bytes mode (helpers mode layout)).length=
      DwordMixedSequence.bytes mode (helpers mode layout))
    (headers : DwordPackets.Intact mode (packets mode layout) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      (∀ descriptor∈arithmetic mode layout,DwordTemplateCollection.Decodes mode descriptor reached.principal.memory) ∧
      (∀ descriptor∈fixed mode layout,MixedFixedTemplates.Decodes mode descriptor reached.principal.memory))
      ((Listing8StateTrace.program mode layout state).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun _reached both => ⟨fun descriptor member => DwordTemplateCollection.decodes mode descriptor _ (both.1 descriptor member),
      fun descriptor member => MixedFixedTemplates.decodes mode descriptor _ (both.2 descriptor member)⟩)
    (all_states mode layout bounds state entry helperImage headers)

theorem at_prefix (mode : Mode) (layout : Layout) (bounds : Listing8StateBounds.Bounds mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (helperImage : ByteMemory.bytesAt state.principal.memory layout.start (DwordMixedSequence.bytes mode (helpers mode layout)).length=
      DwordMixedSequence.bytes mode (helpers mode layout))
    (headers : DwordPackets.Intact mode (packets mode layout) state.principal.memory)
    (before after : List (StringStack.Form mode))
    (cut : (Listing8StateTrace.program mode layout state).map (StringStoreWrites.liftDword mode)=before++after) :
    (∀ descriptor∈arithmetic mode layout,DwordTemplateCollection.Decodes mode descriptor (StringWrites.run mode before state).principal.memory) ∧
    (∀ descriptor∈fixed mode layout,MixedFixedTemplates.Decodes mode descriptor (StringWrites.run mode before state).principal.memory) := by
  have actual := all_decodes mode layout bounds state entry helperImage headers
  rw [cut] at actual
  exact StringTemplateStates.at_prefix mode _ before after state actual

end SmcTuring.Appendix.Listing8StateExecutableTemplates

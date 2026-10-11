module
public import SmcTuring.Native.DwordXorRegionRuns

public section
namespace SmcTuring.Native.DwordXorTemplates

@[expose] def OutsideAll (layouts : List DwordXorHelper.Layout) (address count : Nat) : Prop :=
  ∀ helper∈layouts,address+count≤helper.start ∨ helper.start+18≤address
@[expose] def Decodes (mode : Mode) (layout : DwordXorHelper.Layout) (memory : ByteMemory.Memory) : Prop :=
  StringStack.fetch mode memory layout.start=some (StringStoreWrites.liftDword mode (StringDwordCopy.copy mode (DwordXorHelper.first mode layout))) ∧
  StringStack.fetch mode memory (layout.start+6)=some (StringStoreWrites.liftDword mode (StringDwordXor.canonical mode (DwordXorHelper.middle mode layout))) ∧
  StringStack.fetch mode memory (layout.start+12)=some (StringStoreWrites.liftDword mode (StringDwordCopy.copy mode (DwordXorHelper.third mode layout)))

theorem frame (mode : Mode) (layouts : List DwordXorHelper.Layout) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List LittleEndian.Byte) (intact : DwordXorSequence.Intact mode layouts memory)
    (outside : OutsideAll layouts address packet.length) :
    DwordXorSequence.Intact mode layouts (ByteMemory.putBytes memory address packet) := by
  intro helper member
  rw [ByteMemory.bytes_at_frame]
  · exact intact helper member
  · intro index inside
    have bound := index.isLt
    unfold ByteMemory.Inside at inside
    rcases outside helper member with before | after <;> omega

theorem all_states (mode : Mode) (layouts : List DwordXorHelper.Layout) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode) (intact : DwordXorSequence.Intact mode layouts state.principal.memory)
    (owned : StringStoreRegions.Run mode (OutsideAll layouts) forms state) :
    StringTemplateStates.Run mode (fun reached => DwordXorSequence.Intact mode layouts reached.principal.memory) forms state := by
  induction forms generalizing state with
  | nil => exact intact
  | cons form rest ih =>
    have kept : DwordXorSequence.Intact mode layouts (StringStack.execute mode form state).principal.memory := by
      rw [StringWrites.execute_memory]
      exact frame mode layouts state.principal.memory _ _ intact owned.1
    exact ⟨intact,ih _ kept owned.2⟩

theorem decodes (mode : Mode) (layout : DwordXorHelper.Layout) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory layout.start 18=DwordXorHelper.bytes mode layout) : Decodes mode layout memory := by
  have image : ByteMemory.bytesAt memory layout.start (DwordXorHelper.bytes mode layout).length=DwordXorHelper.bytes mode layout :=
    by simpa only [DwordXorHelper.bytes_length] using current
  have first := ByteWindow.packet memory layout.start [] (DwordCode.encode mode (DwordXorHelper.first mode layout))
    (DwordXor.encode (DwordXorHelper.middle mode layout) ++ DwordCode.encode mode (DwordXorHelper.third mode layout))
    (by simpa [DwordXorHelper.bytes,List.append_assoc] using image)
  have second := ByteWindow.packet memory layout.start (DwordCode.encode mode (DwordXorHelper.first mode layout))
    (DwordXor.encode (DwordXorHelper.middle mode layout)) (DwordCode.encode mode (DwordXorHelper.third mode layout))
    (by simpa [DwordXorHelper.bytes,List.append_assoc] using image)
  have third := ByteWindow.packet memory layout.start
    (DwordCode.encode mode (DwordXorHelper.first mode layout) ++ DwordXor.encode (DwordXorHelper.middle mode layout))
    (DwordCode.encode mode (DwordXorHelper.third mode layout)) []
    (by simpa [DwordXorHelper.bytes,List.append_assoc] using image)
  change ByteMemory.bytesAt memory layout.start 6=DwordCode.encode mode (DwordXorHelper.first mode layout) at first
  change ByteMemory.bytesAt memory (layout.start+6) 6=DwordXor.encode (DwordXorHelper.middle mode layout) at second
  change ByteMemory.bytesAt memory (layout.start+12) 6=DwordCode.encode mode (DwordXorHelper.third mode layout) at third
  refine ⟨StringStack.previous_fetch mode memory layout.start _
    (StringControl.previous_fetch mode memory layout.start _ (StringDwordCopy.copy_encoding mode _ memory layout.start first)),
    StringStack.previous_fetch mode memory (layout.start+6) _
    (StringControl.previous_fetch mode memory (layout.start+6) _ (StringDwordXor.encoding mode memory (layout.start+6) _ second)),
    StringStack.previous_fetch mode memory (layout.start+12) _
    (StringControl.previous_fetch mode memory (layout.start+12) _ (StringDwordCopy.copy_encoding mode _ memory (layout.start+12) third))⟩

theorem all_decodes (mode : Mode) (layouts : List DwordXorHelper.Layout) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode) (intact : DwordXorSequence.Intact mode layouts state.principal.memory)
    (owned : StringStoreRegions.Run mode (OutsideAll layouts) forms state) :
    StringTemplateStates.Run mode (fun reached => ∀ helper∈layouts,Decodes mode helper reached.principal.memory) forms state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun reached all helper member => decodes mode helper reached.principal.memory (all helper member))
    (all_states mode layouts forms state intact owned)

end SmcTuring.Native.DwordXorTemplates

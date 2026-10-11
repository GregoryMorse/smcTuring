module
public import SmcTuring.Appendix.Listing8FailureTemplateRegions

public section
namespace SmcTuring.Appendix.Listing8FailureExecutableTemplates
open Native Listing8FailureLayout Listing8FailureTemplateFields

@[expose] def Property (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) : Prop :=
  DwordTemplateCollection.All (arithmetic mode l) memory ∧
    StringInitTemplates.Intact mode (ownerPC l) memory ∧
    ControlPackets.Intact mode (Listing8FailComparison.sites mode (comparison mode l)) memory ∧
    RelativeCallTemplate.Intact (callPC mode l) memory
@[expose] def Decodes (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) : Prop :=
  (∀ descriptor∈arithmetic mode l,DwordTemplateCollection.Decodes mode descriptor memory) ∧
    StringInitTemplates.Decodes mode (ownerPC l) memory ∧
    (∀ site∈Listing8FailComparison.sites mode (comparison mode l),
      StringStack.fetch mode memory site.pc=some (.previous (ControlPackets.form mode site))) ∧
    RelativeCallTemplate.Decodes mode (callPC mode l) memory

theorem descriptor_count (mode : Mode) (l : Layout) :
    (arithmetic mode l).length+(StringInit.forms mode (ownerPC l) 0).length+
      (Listing8FailComparison.sites mode (comparison mode l)).length=if mode=.x86 then 13 else 16 := by
  cases mode <;> rfl

theorem initial (mode : Mode) (l : Layout) (memory : ByteMemory.Memory)
    (current : Listing8FailureReuseImage.Current mode l memory)
    (callImage : RelativeCallTemplate.Intact (callPC mode l) memory) : Property mode l memory := by
  have resetImage : DwordTemplateCollection.Intact (.binary .store l.start) memory := by
    exact DwordOperandTemplates.initial .store l.start (Relocation.memoryDisp mode (l.start+10) (mask mode l)) 0 memory
      (by simpa only [reset,DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.encode_length,
        DwordArithmetic.length,DwordOperandTemplates.form] using current.resetImage)
  have later := DwordPacketTemplateRuns.initial mode (post mode l) memory current.postHeaders
  refine ⟨?_,StringInitTemplates.initial mode (ownerPC l) l.sentinel memory current.ownerImage,?_,callImage⟩
  · intro descriptor member
    rcases List.mem_cons.mp member with rfl | rest
    · exact resetImage
    · exact later descriptor rest
  · exact ControlPackets.initial_packets mode _ (comparison mode l).start (Listing8FailComparison.chain mode (comparison mode l))
      memory current.comparisonImage

theorem store (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : Property mode l memory) (allowed : Allowed mode l address packet.length) :
    Property mode l (ByteMemory.putBytes memory address packet) := by
  refine ⟨DwordTemplateCollection.store_all _ memory address packet intact.1 (compatible mode l address packet.length allowed),
    StringInitTemplates.frame mode (ownerPC l) memory address packet intact.2.1 (owner_frames mode l address packet.length allowed),
    ?_,RelativeCallTemplate.frame (callPC mode l) memory address packet intact.2.2.2 (call_frames mode l address packet.length allowed)⟩
  intro site member
  have outside := comparison_frames mode l address packet.length allowed site member
  rw [ControlPackets.Current,ByteMemory.bytes_at_frame]
  · exact intact.2.2.1 site member
  · intro index inside
    have bound : index.val<ControlPackets.size mode site := by simpa only [ControlPackets.bytes_length] using index.isLt
    unfold ByteMemory.Inside at inside
    rcases outside with before | after <;> omega

theorem decodes (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) (intact : Property mode l memory) :
    Decodes mode l memory := by
  refine ⟨fun descriptor member => DwordTemplateCollection.decodes mode descriptor memory (intact.1 descriptor member),
    StringInitTemplates.decodes mode (ownerPC l) memory intact.2.1,?_,
    RelativeCallTemplate.decodes mode (callPC mode l) memory intact.2.2.2⟩
  intro site member
  exact StringStack.previous_fetch mode memory site.pc _ (ControlPackets.fetched mode site memory (intact.2.2.1 site member))

/-- All 13/16 original phase boundaries and the pending CALL decode in the
same reached memory, including every temporary native initializer store. -/
theorem all_states (mode : Mode) (l : Layout) (bounds : Listing8FailureBounds.Bounds mode l)
    (sentinelOutside : l.sentinel+mode.wordBytes≤l.start ∨ callPC mode l+5≤l.sentinel)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (current : Listing8FailureReuseImage.Current mode l state.principal.memory)
    (callImage : RelativeCallTemplate.Intact (callPC mode l) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode l reached.principal.memory)
      ((Listing8FailureTrace.program mode l state).map StringStack.Form.previous) state :=
  StringStoreTemplateRuns.preserve mode (Allowed mode l) (Property mode l) _ state (initial mode l _ current callImage)
    (store mode l) (Listing8FailureTemplateRegions.regions mode l bounds sentinelOutside state entry current)

theorem all_decodes (mode : Mode) (l : Layout) (bounds : Listing8FailureBounds.Bounds mode l)
    (sentinelOutside : l.sentinel+mode.wordBytes≤l.start ∨ callPC mode l+5≤l.sentinel)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (current : Listing8FailureReuseImage.Current mode l state.principal.memory)
    (callImage : RelativeCallTemplate.Intact (callPC mode l) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Decodes mode l reached.principal.memory)
      ((Listing8FailureTrace.program mode l state).map StringStack.Form.previous) state :=
  StringTemplateStates.monotone mode _ _ _ state (fun reached intact => decodes mode l reached.principal.memory intact)
    (all_states mode l bounds sentinelOutside state entry current callImage)

theorem at_prefix (mode : Mode) (l : Layout) (bounds : Listing8FailureBounds.Bounds mode l)
    (sentinelOutside : l.sentinel+mode.wordBytes≤l.start ∨ callPC mode l+5≤l.sentinel)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (current : Listing8FailureReuseImage.Current mode l state.principal.memory)
    (callImage : RelativeCallTemplate.Intact (callPC mode l) state.principal.memory)
    (before after : List (StringStack.Form mode))
    (cut : (Listing8FailureTrace.program mode l state).map StringStack.Form.previous=before++after) :
    Decodes mode l (StringWrites.run mode before state).principal.memory := by
  have states := all_decodes mode l bounds sentinelOutside state entry current callImage
  rw [cut] at states
  exact StringTemplateStates.at_prefix mode _ before after state states

end SmcTuring.Appendix.Listing8FailureExecutableTemplates

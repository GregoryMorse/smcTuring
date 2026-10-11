module
public import SmcTuring.Appendix.Listing8ResetTemplateFields

public section
namespace SmcTuring.Appendix.Listing8ResetExecutableTemplates
open Native Listing8ResetLayout Listing8ResetTemplateFields

@[expose] def Property (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) : Prop :=
  FixedStackTemplates.All mode (fixed mode l) memory ∧ DwordTemplateCollection.All (arithmetic mode l) memory ∧
    StringInitTemplates.Intact mode (ownerPC mode l) memory ∧ RelativeCallTemplate.Intact l.callPC memory
@[expose] def Decodes (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) : Prop :=
  (∀ entry∈fixed mode l,FixedStackTemplates.Decodes mode entry memory) ∧
    (∀ descriptor∈arithmetic mode l,DwordTemplateCollection.Decodes mode descriptor memory) ∧
    StringInitTemplates.Decodes mode (ownerPC mode l) memory ∧ RelativeCallTemplate.Decodes mode l.callPC memory

theorem descriptor_count (mode : Mode) (l : Layout) :
    (fixed mode l).length+(arithmetic mode l).length+(StringInit.forms mode (ownerPC mode l) 0).length+1=
      if mode=.x86 then 10 else 13 := by
  rw [fixed_count]
  cases mode <;> rfl

theorem initial (mode : Mode) (l : Layout) (memory : ByteMemory.Memory)
    (current : Listing8ResetPackets.Initial mode l memory) (call : RelativeCallTemplate.Intact l.callPC memory) : Property mode l memory := by
  refine ⟨fixed_initial mode l memory current,?_,StringInitTemplates.initial mode _ _ memory
    (Listing8ResetPackets.owner_current mode l memory current),call⟩
  intro descriptor member
  simp only [arithmetic,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact DwordOperandTemplates.initial .store l.start (storeDisp mode l) (original l) memory
      (Listing8ResetPackets.store_current mode l memory current)
  · exact DwordOperandTemplates.initial .store (markerPC mode l)
      (Relocation.memoryDisp mode (markerPC mode l+10) (markerPC mode l+6)) 0 memory
      (by change ByteMemory.bytesAt memory (markerPC mode l) 10=DwordOwner.bytes mode (markerPC mode l) 0
          rw [←Listing8ResetLayout.marker_bytes]
          exact Listing8ResetPackets.marker_current mode l memory current)

theorem store (mode : Mode) (l : Layout) (bounds : Bounds mode l) (separation : Separation mode l)
    (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : Property mode l memory) (allowed : Listing8ResetStoreRegions.Allowed mode l address packet.length) :
    Property mode l (ByteMemory.putBytes memory address packet) :=
  ⟨FixedStackTemplates.store_all mode _ memory address packet intact.1 (fixed_frames mode l bounds separation _ _ allowed),
    DwordTemplateCollection.store_all _ memory address packet intact.2.1 (arithmetic_compatible mode l bounds separation _ _ allowed),
    StringInitTemplates.frame mode _ memory address packet intact.2.2.1 (owner_frames mode l bounds separation _ _ allowed),
    RelativeCallTemplate.frame _ memory address packet intact.2.2.2 (call_frames mode l bounds separation _ _ allowed)⟩

theorem decodes (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) (intact : Property mode l memory) : Decodes mode l memory :=
  ⟨fun entry member => FixedStackTemplates.decodes mode entry memory (fixed_legal mode l entry member) (intact.1 entry member),
    fun descriptor member => DwordTemplateCollection.decodes mode descriptor memory (intact.2.1 descriptor member),
    StringInitTemplates.decodes mode _ memory intact.2.2.1,RelativeCallTemplate.decodes mode _ memory intact.2.2.2⟩

/-- Every reached reset prefix jointly retains all 9/12 phase instructions and
the pending relative CALL with its current displacement word. -/
theorem all_states (mode : Mode) (l : Layout) (bounds : Bounds mode l) (separation : Separation mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (current : Listing8ResetPackets.Initial mode l state.principal.memory)
    (call : RelativeCallTemplate.Intact l.callPC state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode l reached.principal.memory)
      ((program mode l).map (StringStoreWrites.liftDword mode)) state :=
  StringStoreTemplateRuns.preserve mode (Listing8ResetStoreRegions.Allowed mode l) (Property mode l) _ state
    (initial mode l _ current call) (store mode l bounds separation) (Listing8ResetStoreRegions.regions mode l bounds state entry current)

theorem all_decodes (mode : Mode) (l : Layout) (bounds : Bounds mode l) (separation : Separation mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (current : Listing8ResetPackets.Initial mode l state.principal.memory)
    (call : RelativeCallTemplate.Intact l.callPC state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Decodes mode l reached.principal.memory)
      ((program mode l).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state (fun reached intact => decodes mode l reached.principal.memory intact)
    (all_states mode l bounds separation state entry current call)

theorem at_prefix (mode : Mode) (l : Layout) (bounds : Bounds mode l) (separation : Separation mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (current : Listing8ResetPackets.Initial mode l state.principal.memory)
    (call : RelativeCallTemplate.Intact l.callPC state.principal.memory)
    (before after : List (StringStack.Form mode)) (cut : (program mode l).map (StringStoreWrites.liftDword mode)=before++after) :
    Decodes mode l (StringWrites.run mode before state).principal.memory := by
  have states:=all_decodes mode l bounds separation state entry current call
  rw [cut] at states
  exact StringTemplateStates.at_prefix mode _ before after state states

end SmcTuring.Appendix.Listing8ResetExecutableTemplates

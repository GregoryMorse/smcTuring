module
public import SmcTuring.Appendix.Listing8GlobalControlLayout

public section
namespace SmcTuring.Appendix.Listing8GlobalControlTemplates
open Native Listing8GlobalControlLayout

@[expose] def Property (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) : Prop :=
  FixedStackTemplates.All mode (entries mode origin) memory ∧
    RelativeCallTemplate.Intact (Listing8JumpLayout.callPC mode origin) memory ∧ Listing4StackTemplates.Intact mode origin memory
@[expose] def Decodes (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) : Prop :=
  (∀ entry∈entries mode origin,FixedStackTemplates.Decodes mode entry memory) ∧
    RelativeCallTemplate.Decodes mode (Listing8JumpLayout.callPC mode origin) memory ∧ Listing4StackTemplates.Decodes mode origin memory

theorem descriptor_count (mode : Mode) (origin : Nat) :
    (entries mode origin).length+1+(Listing4StackLayout.forms mode origin).length=if mode=.x86 then 13 else 18 := by
  rw [Listing8GlobalControlLayout.count]
  cases mode <;> rfl

theorem initial (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) (current : Current mode origin memory) : Property mode origin memory :=
  ⟨Listing8GlobalControlLayout.initial mode origin memory current,current.call,Listing4StackTemplates.initial mode origin memory current.stack⟩

theorem store (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : Property mode origin memory) (allowed : Allowed mode origin address packet.length) :
    Property mode origin (ByteMemory.putBytes memory address packet) :=
  ⟨FixedStackTemplates.store_all mode _ memory address packet intact.1 (fixed_frames mode origin _ _ allowed),
    RelativeCallTemplate.frame _ memory address packet intact.2.1 (call_frames mode origin _ _ allowed),
    Listing4StackTemplates.store mode origin memory address packet intact.2.2 (stack_frames mode origin _ _ allowed)⟩

theorem decodes (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) (intact : Property mode origin memory) : Decodes mode origin memory :=
  ⟨fun entry member => FixedStackTemplates.decodes mode entry memory (legal mode origin entry member) (intact.1 entry member),
    RelativeCallTemplate.decodes mode _ memory intact.2.1,Listing4StackTemplates.decodes mode origin memory intact.2.2⟩

theorem all_states (mode : Mode) (origin : Nat) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (intact : Property mode origin state.principal.memory) (regions : StringStoreRegions.Run mode (Allowed mode origin) forms state) :
    StringTemplateStates.Run mode (fun reached => Property mode origin reached.principal.memory) forms state :=
  StringStoreTemplateRuns.preserve mode (Allowed mode origin) (Property mode origin) forms state intact (store mode origin) regions

theorem all_decodes (mode : Mode) (origin : Nat) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (intact : Property mode origin state.principal.memory) (regions : StringStoreRegions.Run mode (Allowed mode origin) forms state) :
    StringTemplateStates.Run mode (fun reached => Decodes mode origin reached.principal.memory) forms state :=
  StringTemplateStates.monotone mode _ _ _ state (fun reached kept => decodes mode origin reached.principal.memory kept)
    (all_states mode origin forms state intact regions)

theorem at_prefix (mode : Mode) (origin : Nat) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (intact : Property mode origin state.principal.memory) (regions : StringStoreRegions.Run mode (Allowed mode origin) forms state)
    (before after : List (StringStack.Form mode)) (cut : forms=before++after) :
    Decodes mode origin (StringWrites.run mode before state).principal.memory := by
  have states:=all_decodes mode origin forms state intact regions
  rw [cut] at states
  exact StringTemplateStates.at_prefix mode _ before after state states

end SmcTuring.Appendix.Listing8GlobalControlTemplates

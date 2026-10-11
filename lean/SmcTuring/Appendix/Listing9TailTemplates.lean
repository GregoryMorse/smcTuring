module
public import SmcTuring.Appendix.Listing9TailTemplateFields

public section
namespace SmcTuring.Appendix.Listing9TailTemplates
open Native Listing9PackedLayout Listing9TailTemplateFields

@[expose] def Property (mode : Mode) (start transitions nodes : Nat) (memory : ByteMemory.Memory) : Prop :=
  FixedStackTemplates.All mode (entries mode start transitions nodes) memory ∧
    StringInitTemplates.Intact mode (saveOwner mode start transitions nodes) memory ∧
    StringInitTemplates.Intact mode (pointerOwner mode start transitions nodes) memory
@[expose] def Decodes (mode : Mode) (start transitions nodes : Nat) (memory : ByteMemory.Memory) : Prop :=
  (∀ entry∈entries mode start transitions nodes,FixedStackTemplates.Decodes mode entry memory) ∧
    StringInitTemplates.Decodes mode (saveOwner mode start transitions nodes) memory ∧
    StringInitTemplates.Decodes mode (pointerOwner mode start transitions nodes) memory

theorem descriptor_count (mode : Mode) (start transitions nodes : Nat) :
    (entries mode start transitions nodes).length+
      (StringInit.forms mode (saveOwner mode start transitions nodes) 0).length+
      (StringInit.forms mode (pointerOwner mode start transitions nodes) 0).length=if mode=.x86 then 6 else 12 := by
  rw [Listing9TailTemplateFields.count]
  cases mode <;> rfl

theorem from_image (mode : Mode) (start transitions nodes : Nat) (memory : ByteMemory.Memory) :
    Property mode start transitions nodes (Listing9Image.memory mode start transitions nodes memory) :=
  ⟨initial_fixed mode start transitions nodes _ (Listing9Image.prologue mode start transitions nodes memory)
    (Listing9Image.epilogue_current mode start transitions nodes memory),
    StringInitTemplates.initial mode _ _ _ (Listing9Image.save_current mode start transitions nodes memory),
    StringInitTemplates.initial mode _ _ _ (Listing9Image.pointer_current mode start transitions nodes memory)⟩

theorem store (mode : Mode) (start transitions nodes : Nat) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : Property mode start transitions nodes memory) (allowed : Allowed mode start transitions nodes address packet.length) :
    Property mode start transitions nodes (ByteMemory.putBytes memory address packet) :=
  ⟨FixedStackTemplates.store_all mode _ memory address packet intact.1 (fixed_frames mode start transitions nodes _ _ allowed),
    StringInitTemplates.frame mode _ memory address packet intact.2.1 (owner_frames mode start transitions nodes _ _ allowed).1,
    StringInitTemplates.frame mode _ memory address packet intact.2.2 (owner_frames mode start transitions nodes _ _ allowed).2⟩

theorem decodes (mode : Mode) (start transitions nodes : Nat) (memory : ByteMemory.Memory)
    (intact : Property mode start transitions nodes memory) : Decodes mode start transitions nodes memory :=
  ⟨fun entry member => FixedStackTemplates.decodes mode entry memory (legal mode start transitions nodes entry member) (intact.1 entry member),
    StringInitTemplates.decodes mode _ memory intact.2.1,StringInitTemplates.decodes mode _ memory intact.2.2⟩

theorem all_states (mode : Mode) (start transitions nodes : Nat) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (intact : Property mode start transitions nodes state.principal.memory)
    (regions : StringStoreRegions.Run mode (Allowed mode start transitions nodes) forms state) :
    StringTemplateStates.Run mode (fun reached => Property mode start transitions nodes reached.principal.memory) forms state :=
  StringStoreTemplateRuns.preserve mode (Allowed mode start transitions nodes) (Property mode start transitions nodes) forms state intact
    (store mode start transitions nodes) regions

theorem all_decodes (mode : Mode) (start transitions nodes : Nat) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (intact : Property mode start transitions nodes state.principal.memory)
    (regions : StringStoreRegions.Run mode (Allowed mode start transitions nodes) forms state) :
    StringTemplateStates.Run mode (fun reached => Decodes mode start transitions nodes reached.principal.memory) forms state :=
  StringTemplateStates.monotone mode _ _ _ state (fun reached kept => decodes mode start transitions nodes reached.principal.memory kept)
    (all_states mode start transitions nodes forms state intact regions)

theorem at_prefix (mode : Mode) (start transitions nodes : Nat) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (intact : Property mode start transitions nodes state.principal.memory)
    (regions : StringStoreRegions.Run mode (Allowed mode start transitions nodes) forms state)
    (before after : List (StringStack.Form mode)) (cut : forms=before++after) :
    Decodes mode start transitions nodes (StringWrites.run mode before state).principal.memory := by
  have states:=all_decodes mode start transitions nodes forms state intact regions
  rw [cut] at states
  exact StringTemplateStates.at_prefix mode _ before after state states

end SmcTuring.Appendix.Listing9TailTemplates

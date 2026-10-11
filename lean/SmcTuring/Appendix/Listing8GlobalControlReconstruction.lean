module
public import SmcTuring.Appendix.Listing8GlobalControlTemplates

public section
namespace SmcTuring.Appendix.Listing8GlobalControlReconstruction
open Native Listing8GlobalControlLayout

theorem window (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (pc count : Nat) (outside : address+packet.length≤pc ∨ pc+count≤address) :
    ByteMemory.bytesAt (ByteMemory.putBytes memory address packet) pc count=ByteMemory.bytesAt memory pc count := by
  apply ByteMemory.bytes_at_frame
  intro index inside
  have bound:=index.isLt
  unfold ByteMemory.Inside at inside
  rcases outside with before | after <;> omega

theorem prefix_iff (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (pc : Nat) (fixed : List LittleEndian.Byte) (outside : address+packet.length≤pc ∨ pc+fixed.length≤address) :
    PayloadTemplate.Prefix (ByteMemory.putBytes memory address packet) pc fixed ↔ PayloadTemplate.Prefix memory pc fixed := by
  simp only [PayloadTemplate.Prefix,window memory address packet pc fixed.length outside]

/-- Global stores leave every early stack opcode fixed even when its two
operand words contain transient values. This is a byte equality in both
directions, rather than an assumed earlier native image. -/
theorem stack_iff (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (allowed : Listing4StackTemplates.Allowed mode origin address packet.length) :
    Listing4StackTemplates.Intact mode origin (ByteMemory.putBytes memory address packet) ↔ Listing4StackTemplates.Intact mode origin memory := by
  cases mode with
  | x86 =>
    change PayloadTemplate.Prefix _ origin [0xc7,0x05] ↔ PayloadTemplate.Prefix _ origin [0xc7,0x05]
    apply prefix_iff
    simp only [Listing4StackTemplates.Allowed,Listing4StackTemplates.Slots,Listing4StackLayout.stptr,
      Listing4StackLayout.returnField,Listing4StackLayout.size,Mode.wordBytes,List.length_cons,List.length_nil] at allowed ⊢
    rcases allowed with slots | outside
    · rcases slots with a | b <;> omega
    · omega
  | x64 =>
    change PairedPayloadTemplate.Intact .x64 _ origin (Listing4StackTemplates.front origin) Listing4StackTemplates.middle [] ↔
      PairedPayloadTemplate.Intact .x64 _ origin (Listing4StackTemplates.front origin) Listing4StackTemplates.middle []
    have ranges : (address+packet.length≤origin ∨ origin+16≤address) ∧
        (address+packet.length≤origin+24 ∨ origin+26≤address) := by
      simp only [Listing4StackTemplates.Allowed,Listing4StackTemplates.Slots,Listing4StackLayout.stptr,
        Listing4StackLayout.returnField,Listing4StackLayout.size,Mode.wordBytes] at allowed
      rcases allowed with slots | outside
      · rcases slots with a | b <;> constructor <;> omega
      · constructor <;> omega
    simp only [PairedPayloadTemplate.Intact]
    have front:=prefix_iff memory address packet origin (Listing4StackTemplates.front origin)
      (by simpa only [Listing4StackTemplates.front_length] using ranges.1)
    have middle:=prefix_iff memory address packet (origin+24) Listing4StackTemplates.middle
      (by simpa only [Listing4StackTemplates.middle,List.length_cons,List.length_nil] using ranges.2)
    simp only [PairedPayloadTemplate.firstField,Listing4StackTemplates.front_length,Mode.wordBytes,Nat.add_assoc] at ⊢
    rw [front,middle]
    simp only [PayloadTemplate.Prefix,ByteMemory.bytesAt,List.ofFn_zero]

theorem store_iff (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (allowed : Allowed mode origin address packet.length) :
    Listing8GlobalControlTemplates.Property mode origin (ByteMemory.putBytes memory address packet) ↔
      Listing8GlobalControlTemplates.Property mode origin memory := by
  have frames:=fixed_frames mode origin address packet.length allowed
  have fixed : FixedStackTemplates.All mode (entries mode origin) (ByteMemory.putBytes memory address packet) ↔
      FixedStackTemplates.All mode (entries mode origin) memory := by
    simp only [FixedStackTemplates.All,FixedStackTemplates.Intact]
    constructor
    all_goals intro current entry member
    all_goals simpa only [window memory address packet _ _ (frames entry member)] using current entry member
  have call:=prefix_iff memory address packet (Listing8JumpLayout.callPC mode origin) [0xe8]
    (by simpa only [List.length_cons,List.length_nil] using call_frames mode origin address packet.length allowed)
  simp only [Listing8GlobalControlTemplates.Property,RelativeCallTemplate.Intact,fixed,call,
    stack_iff mode origin memory address packet (stack_frames mode origin address packet.length allowed)]

/-- Exact emitted store regions and an independently proved reached catalog
reconstruct validity at every earlier boundary of this same execution. -/
theorem all_states (mode : Mode) (origin : Nat) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (regions : StringStoreRegions.Run mode (Allowed mode origin) forms state)
    (ending : Listing8GlobalControlTemplates.Property mode origin (StringWrites.run mode forms state).principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Property mode origin reached.principal.memory) forms state := by
  induction forms generalizing state with
  | nil => exact ending
  | cons form rest ih =>
    have later:=ih (StringStack.execute mode form state) regions.2 ending
    have current : Listing8GlobalControlTemplates.Property mode origin (StringStack.execute mode form state).principal.memory := by
      cases rest with
      | nil => exact later
      | cons => exact later.1
    rw [StringWrites.execute_memory] at current
    exact ⟨(store_iff mode origin state.principal.memory _ _ regions.1).mp current,later⟩

end SmcTuring.Appendix.Listing8GlobalControlReconstruction

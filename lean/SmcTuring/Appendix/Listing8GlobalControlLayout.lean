module
public import SmcTuring.Appendix.Listing8ControlTemplateLayout
public import SmcTuring.Native.RelativeCallTemplate
public import SmcTuring.Appendix.Listing8FullTableImage

public section
namespace SmcTuring.Appendix.Listing8GlobalControlLayout
open Native FixedStackTemplates

@[expose] def entries (mode : Mode) (origin : Nat) : List (Entry mode) :=
  place mode (Listing8JumpLayout.jumpPC mode origin) (Listing8ControlTemplateLayout.prefixInstructions mode origin)++
    place mode (Listing8BootImage.beginPC mode origin)
      (Listing8ControlTemplateLayout.targetInstructions mode origin (Listing8BootImage.beginPC mode origin))++
    place mode (Listing8JumpLayout.failPC mode origin)
      (Listing8ControlTemplateLayout.targetInstructions mode origin (Listing8JumpLayout.failPC mode origin))
@[expose] def Allowed (mode : Mode) (origin address count : Nat) : Prop :=
  Listing4StackTemplates.Slots mode origin address count ∨
    (Listing4EntryLayout.mainPC mode origin≤address ∧ address+count≤Listing8JumpLayout.jumpPC mode origin) ∨
    (Listing8JumpLayout.callPC mode origin+1≤address ∧ address+count≤Listing8JumpLayout.callPC mode origin+5) ∨
    Listing8FullTableImage.start mode origin≤address

structure Current (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) : Prop where
  stack : ByteMemory.bytesAt memory origin (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode origin
  before : ByteMemory.bytesAt memory (Listing8JumpLayout.jumpPC mode origin)
    (Listing8JumpLayout.prefixBytes mode origin).length=Listing8JumpLayout.prefixBytes mode origin
  call : RelativeCallTemplate.Intact (Listing8JumpLayout.callPC mode origin) memory
  begin : ByteMemory.bytesAt memory (Listing8BootImage.beginPC mode origin) (Listing4TargetLayout.size mode)=
    Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin)
  fail : ByteMemory.bytesAt memory (Listing8JumpLayout.failPC mode origin) (Listing4TargetLayout.size mode)=
    Listing4TargetLayout.bytes mode origin (Listing8JumpLayout.failPC mode origin)

theorem ordered (mode : Mode) (origin : Nat) :
    origin+Listing4StackLayout.size mode≤Listing8BootImage.beginPC mode origin ∧
    Listing8BootImage.beginPC mode origin+Listing4TargetLayout.size mode=Listing4EntryLayout.mainPC mode origin ∧
    Listing4EntryLayout.mainPC mode origin≤Listing8JumpLayout.jumpPC mode origin ∧
    Listing8JumpLayout.jumpPC mode origin≤Listing8JumpLayout.callPC mode origin ∧
    Listing8JumpLayout.callPC mode origin+5=Listing8JumpLayout.failPC mode origin ∧
    Listing8JumpLayout.failPC mode origin+Listing4TargetLayout.size mode=Listing8FullTableImage.start mode origin := by
  cases mode <;> simp [Listing4StackLayout.size,Listing8BootImage.beginPC,Listing4JumpLayout.beginPC,Listing4JumpLayout.callPC,
    Listing4JumpLayout.jumpPC,Listing4JumpLayout.prefixSize,Listing4TargetLayout.size,Listing4EntryLayout.mainPC,Listing4EntryLayout.size,
    Listing8JumpLayout.jumpPC,Listing8JumpLayout.callPC,Listing8JumpLayout.failPC,Listing8FullTableImage.start,Listing8FailLayout.endPC]
theorem count (mode : Mode) (origin : Nat) : (entries mode origin).length=if mode=.x86 then 11 else 13 := by
  simp only [entries,List.length_append,placed_count,Listing8ControlTemplateLayout.targetInstructions,List.length_cons,List.length_nil]
  cases mode <;> rfl

theorem legal (mode : Mode) (origin : Nat) : ∀ entry∈entries mode origin,Legal mode entry.instruction := by
  intro entry member
  simp only [entries,List.mem_append] at member
  rcases member with (before | begin) | fail
  · apply placed_legal mode _ _ _ entry before
    cases mode <;> simp [Listing8ControlTemplateLayout.prefixInstructions,Legal,native,StringForm.Legal]
  all_goals apply placed_legal mode _ _ _ entry (by assumption)
  all_goals cases mode
  all_goals simp [Listing8ControlTemplateLayout.targetInstructions,Listing8ControlTemplateLayout.targetAdjust,Legal,native,StringForm.Legal,StringOperands.subtract]

theorem bounds (mode : Mode) (origin : Nat) (entry : Entry mode) (member : entry∈entries mode origin) :
    origin+Listing4StackLayout.size mode≤entry.pc ∧
      (entry.pc+(FixedStackTemplates.encode mode entry.instruction).length≤Listing4EntryLayout.mainPC mode origin ∨
        (Listing8JumpLayout.jumpPC mode origin≤entry.pc ∧ entry.pc+(FixedStackTemplates.encode mode entry.instruction).length≤Listing8JumpLayout.callPC mode origin) ∨
        (Listing8JumpLayout.failPC mode origin≤entry.pc ∧ entry.pc+(FixedStackTemplates.encode mode entry.instruction).length≤Listing8FullTableImage.start mode origin)) := by
  have ordering:=ordered mode origin
  simp only [entries,List.mem_append] at member
  rcases member with (before | begin) | fail
  · have h:=placed_bounds mode _ _ entry before
    rw [Listing8ControlTemplateLayout.prefix_encoding,Listing8JumpLayout.prefix_length] at h
    change Listing8JumpLayout.jumpPC mode origin≤entry.pc ∧ entry.pc+(FixedStackTemplates.encode mode entry.instruction).length≤Listing8JumpLayout.callPC mode origin at h
    exact ⟨by omega,Or.inr (Or.inl h)⟩
  · have h:=placed_bounds mode _ _ entry begin
    rw [Listing8ControlTemplateLayout.target_encoding,Listing4TargetLayout.bytes_length] at h
    exact ⟨by omega,Or.inl (by omega)⟩
  · have h:=placed_bounds mode _ _ entry fail
    rw [Listing8ControlTemplateLayout.target_encoding,Listing4TargetLayout.bytes_length] at h
    exact ⟨by omega,Or.inr (Or.inr (by constructor <;> omega))⟩

theorem fixed_frames (mode : Mode) (origin address size : Nat) (allowed : Allowed mode origin address size) :
    OutsideAll mode (entries mode origin) address size := by
  have ordering:=ordered mode origin
  intro entry member
  have windows:=bounds mode origin entry member
  rcases allowed with slots | body | call | later
  · exact Or.inl (Nat.le_trans (Listing8ControlTemplateLayout.slot_upper mode origin address size slots) windows.1)
  all_goals rcases windows.2 with early | ⟨before,stop⟩ | ⟨after,stop⟩
  all_goals omega

theorem call_frames (mode : Mode) (origin address size : Nat) (allowed : Allowed mode origin address size) :
    address+size≤Listing8JumpLayout.callPC mode origin ∨ Listing8JumpLayout.callPC mode origin+1≤address := by
  have ordering:=ordered mode origin
  rcases allowed with slots | body | call | later
  · have bound:=Listing8ControlTemplateLayout.slot_upper mode origin address size slots;omega
  all_goals omega

theorem stack_frames (mode : Mode) (origin address size : Nat) (allowed : Allowed mode origin address size) :
    Listing4StackTemplates.Allowed mode origin address size := by
  have ordering:=ordered mode origin
  rcases allowed with slots | body | call | later
  · exact Or.inl slots
  all_goals exact Or.inr (Or.inr (by omega))

theorem initial (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory) (current : Current mode origin memory) :
    All mode (entries mode origin) memory := by
  have before:=placed_initial mode (Listing8JumpLayout.jumpPC mode origin) (Listing8ControlTemplateLayout.prefixInstructions mode origin) memory (by rw [Listing8ControlTemplateLayout.prefix_encoding];exact current.before)
  have begin:=placed_initial mode (Listing8BootImage.beginPC mode origin) (Listing8ControlTemplateLayout.targetInstructions mode origin (Listing8BootImage.beginPC mode origin)) memory (by rw [Listing8ControlTemplateLayout.target_encoding,Listing4TargetLayout.bytes_length];exact current.begin)
  have fail:=placed_initial mode (Listing8JumpLayout.failPC mode origin) (Listing8ControlTemplateLayout.targetInstructions mode origin (Listing8JumpLayout.failPC mode origin)) memory (by rw [Listing8ControlTemplateLayout.target_encoding,Listing4TargetLayout.bytes_length];exact current.fail)
  intro entry member
  simp only [entries,List.mem_append] at member
  rcases member with (a | b) | c
  · exact before entry a
  · exact begin entry b
  · exact fail entry c

end SmcTuring.Appendix.Listing8GlobalControlLayout

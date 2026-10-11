module
public import SmcTuring.Appendix.Listing8JumpSlotRegions

public section
namespace SmcTuring.Appendix.Listing8ControlTemplateLayout
open Native FixedStackTemplates Listing4StackLayout

@[expose] def prefixInstructions (mode : Mode) (origin : Nat) : List (Instruction mode) :=
  match mode with
  | .x86 => [FixedStackTemplates.native .x86 (Listing8JumpLayout.exchange .x86 origin)]
  | .x64 => [FixedStackTemplates.native .x64 (Listing8JumpLayout.exchange .x64 origin),
      .addSmall (Relocation.memoryDisp .x64 (Listing8JumpLayout.jumpPC .x64 origin+7+8) (returnField .x64 origin)) 18,
      FixedStackTemplates.native .x64 (Listing8JumpLayout.exchangeSaved origin)]
@[expose] def targetAdjust (mode : Mode) (origin target : Nat) : Instruction mode :=
  match mode with
  | .x86 => .addSmall (Relocation.memoryDisp .x86 (target+6+7) (stptr .x86 origin)) 4
  | .x64 => .string (StringOperands.subtract .x64 (target+7) (stptr .x64 origin) 10)
@[expose] def targetInstructions (mode : Mode) (origin target : Nat) : List (Instruction mode) :=
  [FixedStackTemplates.native mode (Listing4TargetLayout.first mode origin target),targetAdjust mode origin target,
    FixedStackTemplates.native mode (Listing4TargetLayout.third mode origin target),FixedStackTemplates.native mode (Listing4TargetLayout.fourth mode origin target),
    FixedStackTemplates.native mode (Listing4TargetLayout.fifth mode origin target)]
@[expose] def entries (mode : Mode) (origin : Nat) (failed : Bool) : List (Entry mode) :=
  place mode (Listing8JumpLayout.jumpPC mode origin) (prefixInstructions mode origin)++
    [⟨Listing8JumpLayout.callPC mode origin,FixedStackTemplates.native mode (Listing8JumpLayout.call mode origin failed)⟩]++
    place mode (Listing8JumpReturn.target mode origin failed) (targetInstructions mode origin (Listing8JumpReturn.target mode origin failed))

theorem prefix_encoding (mode : Mode) (origin : Nat) :
    FixedStackTemplates.bytes mode (prefixInstructions mode origin)=Listing8JumpLayout.prefixBytes mode origin := by
  cases mode <;> simp [FixedStackTemplates.bytes,prefixInstructions,FixedStackTemplates.encode,FixedStackTemplates.native,StringForm.encode,Listing8JumpLayout.prefixBytes,List.append_assoc]

theorem target_encoding (mode : Mode) (origin target : Nat) :
    FixedStackTemplates.bytes mode (targetInstructions mode origin target)=Listing4TargetLayout.bytes mode origin target := by
  cases mode <;> simp [FixedStackTemplates.bytes,targetInstructions,targetAdjust,FixedStackTemplates.encode,FixedStackTemplates.native,StringForm.encode,
    Listing4TargetLayout.bytes,Listing4TargetLayout.adjustBytes,List.append_assoc]

theorem descriptor_count (mode : Mode) (origin : Nat) (failed : Bool) :
    (entries mode origin failed).length=if mode=.x86 then 7 else 9 := by
  simp only [entries,List.length_append,placed_count,List.length_cons,List.length_nil,targetInstructions]
  cases mode <;> rfl

theorem legal (mode : Mode) (origin : Nat) (failed : Bool) :
    ∀ entry∈entries mode origin failed,FixedStackTemplates.Legal mode entry.instruction := by
  intro entry member
  simp only [entries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with before | rfl | after
  · apply placed_legal mode _ _ _ entry before
    cases mode <;> simp [prefixInstructions,FixedStackTemplates.Legal,FixedStackTemplates.native,StringForm.Legal]
  · exact True.intro
  · apply placed_legal mode _ _ _ entry after
    cases mode <;> simp [targetInstructions,targetAdjust,FixedStackTemplates.Legal,FixedStackTemplates.native,StringForm.Legal,StringOperands.subtract]

theorem initial (mode : Mode) (origin : Nat) (failed : Bool) (memory : ByteMemory.Memory)
    (current : Listing8JumpReturn.Current mode origin failed memory) : All mode (entries mode origin failed) memory := by
  have before:=placed_initial mode (Listing8JumpLayout.jumpPC mode origin) (prefixInstructions mode origin) memory
    (by rw [prefix_encoding];exact current.prefixImage)
  have after:=placed_initial mode (Listing8JumpReturn.target mode origin failed)
    (targetInstructions mode origin (Listing8JumpReturn.target mode origin failed)) memory
    (by rw [target_encoding,Listing4TargetLayout.bytes_length];exact current.targetImage)
  intro entry member
  simp only [entries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with earlier | rfl | later
  · exact before entry earlier
  · exact current.callImage
  · exact after entry later

theorem bounds (mode : Mode) (origin : Nat) (failed : Bool) (entry : Entry mode) (member : entry∈entries mode origin failed) :
    origin+size mode≤entry.pc := by
  have before : origin+size mode≤Listing8JumpLayout.jumpPC mode origin := by
    cases mode <;> simp [size,Listing8JumpLayout.jumpPC]
  simp only [entries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with earlier | rfl | later
  · have lower:=(placed_bounds mode _ _ entry earlier).1;omega
  · change origin+size mode≤Listing8JumpLayout.callPC mode origin
    unfold Listing8JumpLayout.callPC
    omega
  · have lower:=(placed_bounds mode _ _ entry later).1
    have placement:=Listing8JumpReturn.placement mode origin failed
    omega

theorem slot_upper (mode : Mode) (origin address count : Nat) (slots : Listing4StackTemplates.Slots mode origin address count) :
    address+count≤origin+size mode := by
  cases mode <;> simp only [Listing4StackTemplates.Slots,stptr,returnField,Mode.wordBytes,size] at slots ⊢
  all_goals rcases slots with a | b <;> omega

theorem frames (mode : Mode) (origin : Nat) (failed : Bool) (address count : Nat)
    (slots : Listing4StackTemplates.Slots mode origin address count) : OutsideAll mode (entries mode origin failed) address count := by
  intro entry member
  exact Or.inl (Nat.le_trans (slot_upper mode origin address count slots) (bounds mode origin failed entry member))

end SmcTuring.Appendix.Listing8ControlTemplateLayout

module
public import SmcTuring.Appendix.Listing8ControlTemplateLayout

public section
namespace SmcTuring.Appendix.Listing8ControlExecutableTemplates
open Native Listing8ControlTemplateLayout

@[expose] def Property (mode : Mode) (origin : Nat) (failed : Bool) (memory : ByteMemory.Memory) : Prop :=
  FixedStackTemplates.All mode (entries mode origin failed) memory ∧ Listing4StackTemplates.Intact mode origin memory
@[expose] def Decodes (mode : Mode) (origin : Nat) (failed : Bool) (memory : ByteMemory.Memory) : Prop :=
  (∀ entry∈entries mode origin failed,FixedStackTemplates.Decodes mode entry memory) ∧ Listing4StackTemplates.Decodes mode origin memory

theorem descriptor_count (mode : Mode) (origin : Nat) (failed : Bool) :
    (entries mode origin failed).length+(Listing4StackLayout.forms mode origin).length=if mode=.x86 then 8 else 13 := by
  rw [Listing8ControlTemplateLayout.descriptor_count]
  cases mode <;> rfl

theorem initial (mode : Mode) (origin : Nat) (failed : Bool) (memory : ByteMemory.Memory)
    (current : Listing8JumpReturn.Current mode origin failed memory) : Property mode origin failed memory :=
  ⟨Listing8ControlTemplateLayout.initial mode origin failed memory current,Listing4StackTemplates.initial mode origin memory current.stackImage⟩

theorem store (mode : Mode) (origin : Nat) (failed : Bool) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : Property mode origin failed memory) (slots : Listing4StackTemplates.Slots mode origin address packet.length) :
    Property mode origin failed (ByteMemory.putBytes memory address packet) :=
  ⟨FixedStackTemplates.store_all mode _ memory address packet intact.1 (frames mode origin failed address packet.length slots),
    Listing4StackTemplates.store mode origin memory address packet intact.2 (Or.inl slots)⟩

theorem decodes (mode : Mode) (origin : Nat) (failed : Bool) (memory : ByteMemory.Memory) (intact : Property mode origin failed memory) :
    Decodes mode origin failed memory :=
  ⟨fun entry member => FixedStackTemplates.decodes mode entry memory (legal mode origin failed entry member) (intact.1 entry member),
    Listing4StackTemplates.decodes mode origin memory intact.2⟩

/-- All literal CALL/target instructions and the original stack declaration
decode jointly at every reached boundary, including transient SP/return stores. -/
theorem all_states (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (current : Listing8JumpReturn.Current mode origin failed state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode origin failed reached.principal.memory)
      (Listing8JumpReturn.program mode origin failed) state :=
  StringStoreTemplateRuns.preserve mode (Listing4StackTemplates.Slots mode origin) (Property mode origin failed) _ state
    (initial mode origin failed _ current) (store mode origin failed) (Listing8JumpSlotRegions.complete mode origin failed state entry capacity current)

theorem all_decodes (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (current : Listing8JumpReturn.Current mode origin failed state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Decodes mode origin failed reached.principal.memory)
      (Listing8JumpReturn.program mode origin failed) state :=
  StringTemplateStates.monotone mode _ _ _ state (fun reached intact => decodes mode origin failed reached.principal.memory intact)
    (all_states mode origin failed state entry capacity current)

theorem at_prefix (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (current : Listing8JumpReturn.Current mode origin failed state.principal.memory)
    (before after : List (StringStack.Form mode)) (cut : Listing8JumpReturn.program mode origin failed=before++after) :
    Decodes mode origin failed (StringWrites.run mode before state).principal.memory := by
  have states:=all_decodes mode origin failed state entry capacity current
  rw [cut] at states
  exact StringTemplateStates.at_prefix mode _ before after state states

end SmcTuring.Appendix.Listing8ControlExecutableTemplates

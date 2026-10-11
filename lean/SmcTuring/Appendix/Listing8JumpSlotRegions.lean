module
public import SmcTuring.Appendix.Listing4TargetSlotRegions
public import SmcTuring.Appendix.Listing8JumpReturnWrites

public section
namespace SmcTuring.Appendix.Listing8JumpSlotRegions
open Native Listing4StackLayout Listing8JumpLayout Listing8JumpEffects

/-- Present stack declaration bytes derive the exact CALL destination slot;
every earlier temporary SP store is in one complete original operand. -/
theorem jump (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (jumpPC mode origin))
    (capacity : failPC mode origin<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory origin (size mode)=Listing4StackLayout.bytes mode origin) :
    StringStoreRegions.Run mode (Listing4StackTemplates.Slots mode origin) (forms mode origin failed) state := by
  have stFits : stptr mode origin<2^(8*mode.wordBytes) := by
    have cap:=stack_capacity mode origin capacity
    have bound:=stptr_fits mode origin cap;omega
  have savedFits : returnField mode origin<2^(8*mode.wordBytes) := by
    have cap:=stack_capacity mode origin capacity
    cases mode <;> simp [returnField,size,Mode.wordBytes] at cap ⊢ <;> omega
  have stOwned:=StringFieldWrites.word_owned mode (stptr mode origin) (stptr mode origin+mode.wordBytes) _ stFits ⟨Nat.le_refl _,Nat.le_refl _⟩
  have savedOwned:=StringFieldWrites.word_owned mode (returnField mode origin) (returnField mode origin+mode.wordBytes) _ savedFits ⟨Nat.le_refl _,Nat.le_refl _⟩
  have first:=Listing8JumpWrites.exchange_write mode (stptr mode origin) (stptr mode origin+mode.wordBytes)
    (jumpPC mode origin) (stptr mode origin) state entry (first_reach mode origin) stOwned
  have called:=Listing8JumpWrites.native_write mode (returnField mode origin) (returnField mode origin+mode.wordBytes)
    (call mode origin failed) (prefixEnd mode origin state) (by
      change StringWrites.WordOwned mode _ _ ((prefixEnd mode origin state).principal.stack-Arithmetic.encodeNat mode mode.wordBytes)
      rw [prefix_effect mode origin state entry capacity current,Listing4JumpLayout.stack_decrement]
      exact savedOwned)
  have callRegion:=Listing4TargetSlotRegions.at_field mode origin _ _ _ called
    (BoundedStoreRegions.native_length mode _ _) (Or.inr rfl)
  have firstRegion:=Listing4TargetSlotRegions.at_field mode origin _ _ _ first
    (BoundedStoreRegions.native_length mode _ _) (Or.inl rfl)
  cases mode with
  | x86 => exact ⟨firstRegion,callRegion,trivial⟩
  | x64 =>
    have pc1 : (exchanged .x64 origin state).principal.pc=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7) := by
      rw [exchanged_effect .x64 origin state entry capacity current];rfl
    have middle:=Listing8JumpWrites.adjust_write (returnField .x64 origin) (returnField .x64 origin+8) origin
      (exchanged .x64 origin state) pc1 savedOwned
    have pc2 : (adjusted origin state).principal.pc=Arithmetic.encodeNat .x64 (jumpPC .x64 origin+7+8) := by
      rw [adjusted_effect origin state entry capacity current]
    have third:=Listing8JumpWrites.exchange_write .x64 (returnField .x64 origin) (returnField .x64 origin+8)
      (jumpPC .x64 origin+7+8) (returnField .x64 origin) (adjusted origin state) pc2 (fun _ => saved_reach origin) savedOwned
    have middleRegion:=Listing4TargetSlotRegions.at_field .x64 origin _ _ _ middle (LittleEndian.word_encode_length _ _) (Or.inr rfl)
    have thirdRegion:=Listing4TargetSlotRegions.at_field .x64 origin _ _ _ third (BoundedStoreRegions.native_length .x64 _ _) (Or.inr rfl)
    exact ⟨firstRegion,middleRegion,thirdRegion,callRegion,trivial⟩

theorem complete (mode : Mode) (origin : Nat) (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (jumpPC mode origin))
    (capacity : failPC mode origin<2^(8*mode.wordBytes))
    (current : Listing8JumpReturn.Current mode origin failed state.principal.memory) :
    StringStoreRegions.Run mode (Listing4StackTemplates.Slots mode origin) (Listing8JumpReturn.program mode origin failed) state := by
  have first:=jump mode origin failed state entry capacity current.stackImage
  have last:=Listing4TargetSlotRegions.regions mode origin (Listing8JumpReturn.target mode origin failed)
    (Arithmetic.encodeNat mode (failPC mode origin)) (Listing8JumpReturn.targetSeed mode origin state)
    (Listing8JumpReturn.ranges mode origin failed) (stack_capacity mode origin capacity) current.stackImage
  rw [←Listing8JumpReturn.call_shape mode origin failed state entry capacity current] at last
  rw [Listing8JumpReturn.program,StringStoreRegions.append,
    StringWrites.trace_run_eq mode (Listing8JumpTrace.trace mode origin failed state entry capacity
      current.stackImage current.prefixImage current.callImage)]
  exact ⟨first,last⟩

end SmcTuring.Appendix.Listing8JumpSlotRegions

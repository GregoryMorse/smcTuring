module
public import SmcTuring.Appendix.Listing4StackTemplates
public import SmcTuring.Appendix.Listing4TargetWrites
public import SmcTuring.Native.BoundedStoreRegions

public section
namespace SmcTuring.Appendix.Listing4TargetSlotRegions
open Native Listing4StackLayout Listing4TargetLayout Listing4TargetEffects

theorem at_field (mode : Mode) (start field : Nat) (form : StringStack.Form mode) (state : StringExecution.State mode)
    (inside : StringWrites.CodeWrite mode field (field+mode.wordBytes) form state)
    (length : (StringWrites.packet mode form state).bytes.length=mode.wordBytes)
    (belongs : field=stptr mode start ∨ field=returnField mode start) :
    Listing4StackTemplates.Slots mode start (StringWrites.packet mode form state).address (StringWrites.packet mode form state).bytes.length := by
  apply BoundedStoreRegions.packet mode (Listing4StackTemplates.Slots mode start) field mode.wordBytes form state inside length
  rcases belongs with rfl | rfl
  · exact Or.inl ⟨Nat.le_refl _,Nat.le_refl _⟩
  · exact Or.inr ⟨Nat.le_refl _,Nat.le_refl _⟩

/-- Every complete target store is in one of the two actual stack operands;
the gap between x64 operands is excluded by the exact reached addresses. -/
theorem regions (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode)
    (ranges : Ranges mode start target) (capacity : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt seed.principal.memory start (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode start) :
    StringStoreRegions.Run mode (Listing4StackTemplates.Slots mode start) (forms mode start target) (entry mode start target ret seed) := by
  have stFits : stptr mode start<2^(8*mode.wordBytes) := by
    have bound:=stptr_fits mode start capacity;omega
  have retFits : returnField mode start<2^(8*mode.wordBytes) := by
    cases mode <;> simp [returnField,Listing4StackLayout.size,Mode.wordBytes] at capacity ⊢ <;> omega
  have stOwned:=StringFieldWrites.word_owned mode (stptr mode start) (stptr mode start+mode.wordBytes) _ stFits ⟨Nat.le_refl _,Nat.le_refl _⟩
  have retOwned:=StringFieldWrites.word_owned mode (returnField mode start) (returnField mode start+mode.wordBytes) _ retFits ⟨Nat.le_refl _,Nat.le_refl _⟩
  have first:=Listing8JumpWrites.exchange_write mode (stptr mode start) (stptr mode start+mode.wordBytes) target (stptr mode start)
    (entry mode start target ret seed) rfl ranges.first stOwned
  have pc1 : (swapped mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (target+StackMemory.size mode) := by
    rw [swapped_effect mode start target ret seed ranges capacity]
  have middle : StringWrites.CodeWrite mode (stptr mode start) (stptr mode start+mode.wordBytes)
      (adjust mode start target) (swapped mode start target ret seed) := by
    cases mode with
    | x86 =>
      exact StackFieldWrites.add .x86 _ _ (target+6) (stptr .x86 start) 4
        (swapped .x86 start target ret seed) pc1 (by intro impossible;cases impossible) stOwned
    | x64 =>
      exact StringFieldWrites.subtract .x64 _ _ (target+7) (stptr .x64 start) 10
        (swapped .x64 start target ret seed) pc1 ranges.adjust stOwned
  have middleLength : (StringWrites.packet mode (adjust mode start target) (swapped mode start target ret seed)).bytes.length=mode.wordBytes := by
    cases mode with
    | x86 => exact LittleEndian.word_encode_length _ _
    | x64 => exact StringFieldWrites.subtract_size .x64 (target+7) (stptr .x64 start) 10 (swapped .x64 start target ret seed)
  have pc2 : (adjusted mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (thirdPC mode target) := by
    rw [adjusted_effect mode start target ret seed ranges capacity]
  have third:=StackFieldWrites.memory mode .exchangeAcc (by decide) (stptr mode start) (stptr mode start+mode.wordBytes)
    (thirdPC mode target) (stptr mode start) (adjusted mode start target ret seed) pc2
    (by simpa only [fourthPC,show Native.instructionLength mode (.memory .exchangeAcc 0)=StackMemory.size mode by cases mode <;> rfl] using ranges.third) stOwned
  have pc3 : (exchanged mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (fourthPC mode target) := by
    rw [exchanged_effect mode start target ret seed ranges capacity]
  have fourth:=StackFieldWrites.memory mode .storeAcc (by decide) (returnField mode start) (returnField mode start+mode.wordBytes)
    (fourthPC mode target) (returnField mode start) (exchanged mode start target ret seed) pc3
    (by simpa only [fifthPC,show Native.instructionLength mode (.memory .storeAcc 0)=StackMemory.size mode by cases mode <;> rfl] using ranges.fourth) retOwned
  have pc4 : (stored mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (fifthPC mode target) := by
    rw [stored_effect mode start target ret seed ranges capacity current]
  have fifth:=StackFieldWrites.memory mode .exchangeAcc (by decide) (stptr mode start) (stptr mode start+mode.wordBytes)
    (fifthPC mode target) (stptr mode start) (stored mode start target ret seed) pc4
    (by simpa only [endPC,show Native.instructionLength mode (.memory .exchangeAcc 0)=StackMemory.size mode by cases mode <;> rfl] using ranges.fifth) stOwned
  exact ⟨at_field mode start _ _ _ first (BoundedStoreRegions.native_length mode _ _) (Or.inl rfl),
    at_field mode start _ _ _ middle middleLength (Or.inl rfl),
    at_field mode start _ _ _ third (BoundedStoreRegions.native_length mode _ _) (Or.inl rfl),
    at_field mode start _ _ _ fourth (BoundedStoreRegions.native_length mode _ _) (Or.inr rfl),
    at_field mode start _ _ _ fifth (BoundedStoreRegions.native_length mode _ _) (Or.inl rfl),trivial⟩

end SmcTuring.Appendix.Listing4TargetSlotRegions

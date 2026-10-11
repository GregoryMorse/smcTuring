module
public import SmcTuring.Appendix.Listing4StackWrites

public section
namespace SmcTuring.Appendix.Listing4TargetWrites
open Native Listing4StackLayout Listing4TargetLayout Listing4TargetEffects

theorem owned (mode : Mode) (codeStart codeEnd start target : Nat) (ret : Word mode) (seed : StringExecution.State mode)
    (ranges : Ranges mode start target)
    (capacity : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (inside : codeStart≤start ∧ start+Listing4StackLayout.size mode≤codeEnd)
    (current : ByteMemory.bytesAt seed.principal.memory start (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode start) :
    StringWrites.OwnedRun mode codeStart codeEnd (forms mode start target) (entry mode start target ret seed) := by
  have ⟨stptrOwned,savedOwned⟩:=Listing4StackWrites.slots mode codeStart codeEnd start capacity inside
  have first:=Listing8JumpWrites.exchange_write mode codeStart codeEnd target (stptr mode start)
    (entry mode start target ret seed) rfl ranges.first stptrOwned
  have pc1 : (swapped mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (target+StackMemory.size mode) := by
    rw [swapped_effect mode start target ret seed ranges capacity]
  have middle : StringWrites.CodeWrite mode codeStart codeEnd (adjust mode start target) (swapped mode start target ret seed) := by
    cases mode with
    | x86 =>
      exact StackFieldWrites.add .x86 codeStart codeEnd (target+6) (stptr .x86 start) 4
        (swapped .x86 start target ret seed) pc1 (by intro impossible;cases impossible) stptrOwned
    | x64 =>
      exact StringFieldWrites.subtract .x64 codeStart codeEnd (target+7) (stptr .x64 start) 10
        (swapped .x64 start target ret seed) pc1 ranges.adjust stptrOwned
  have pc2 : (adjusted mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (thirdPC mode target) := by
    rw [adjusted_effect mode start target ret seed ranges capacity]
  have third:=StackFieldWrites.memory mode .exchangeAcc (by decide) codeStart codeEnd (thirdPC mode target) (stptr mode start)
    (adjusted mode start target ret seed) pc2 (by simpa only [fourthPC,show Native.instructionLength mode (.memory .exchangeAcc 0)=StackMemory.size mode by cases mode <;> rfl] using ranges.third) stptrOwned
  have pc3 : (exchanged mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (fourthPC mode target) := by
    rw [exchanged_effect mode start target ret seed ranges capacity]
  have fourth:=StackFieldWrites.memory mode .storeAcc (by decide) codeStart codeEnd (fourthPC mode target) (returnField mode start)
    (exchanged mode start target ret seed) pc3 (by simpa only [fifthPC,show Native.instructionLength mode (.memory .storeAcc 0)=StackMemory.size mode by cases mode <;> rfl] using ranges.fourth) savedOwned
  have pc4 : (stored mode start target ret seed).principal.pc=Arithmetic.encodeNat mode (fifthPC mode target) := by
    rw [stored_effect mode start target ret seed ranges capacity current]
  have fifth:=StackFieldWrites.memory mode .exchangeAcc (by decide) codeStart codeEnd (fifthPC mode target) (stptr mode start)
    (stored mode start target ret seed) pc4 (by simpa only [endPC,show Native.instructionLength mode (.memory .exchangeAcc 0)=StackMemory.size mode by cases mode <;> rfl] using ranges.fifth) stptrOwned
  exact ⟨first,middle,third,fourth,fifth,trivial⟩

theorem run (mode : Mode) (start target : Nat) (ret : Word mode) (seed : StringExecution.State mode)
    (ranges : Ranges mode start target)
    (capacity : start+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (targetCapacity : target+Listing4TargetLayout.size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt seed.principal.memory start (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode start)
    (after : start+Listing4StackLayout.size mode≤target)
    (targetCurrent : ByteMemory.bytesAt seed.principal.memory target (Listing4TargetLayout.size mode)=bytes mode start target) :
    StringWrites.run mode (forms mode start target) (entry mode start target ret seed)=finish mode start target ret seed :=
  StringWrites.trace_run_eq mode (Listing4TargetTrace.trace mode start target ret seed ranges capacity targetCapacity current after targetCurrent)

/-- Every architectural store in the complete printed bootstrap is in its
emitted stack fields. Future CALL/target states are derived by execution. -/
theorem entry_owned (mode : Mode) (codeStart codeEnd start : Nat) (seed : StringExecution.State mode)
    (capacity : Listing4EntryLayout.mainPC mode start<2^(8*mode.wordBytes))
    (inside : codeStart≤start ∧ start+Listing4StackLayout.size mode≤codeEnd) :
    StringWrites.OwnedRun mode codeStart codeEnd (Listing4EntryLayout.forms mode start) (Listing4Entry.initial mode start seed) := by
  have boot:=Listing4StackWrites.boot_owned mode codeStart codeEnd start (Listing4Entry.initial mode start seed) rfl
    (Listing4EntryLayout.boot_capacity mode start capacity) inside (Listing4Entry.boot_current mode start seed)
  have bootRun:=StringWrites.trace_run_eq mode (Listing4Boot.trace mode start (Listing4Entry.initial mode start seed) rfl
    (Listing4EntryLayout.boot_capacity mode start capacity) (Listing4Entry.boot_current mode start seed))
  have target:=owned mode codeStart codeEnd start (Listing4JumpLayout.beginPC mode start)
    (Arithmetic.encodeNat mode (Listing4JumpLayout.beginPC mode start)) (Listing4Entry.targetSeed mode start seed)
    (Listing4EntryLayout.begin_ranges mode start) (Listing4EntryLayout.stack_capacity mode start capacity) inside
    (Listing4Entry.stack_current mode start seed)
  rw [←Listing4Entry.call_shape mode start seed capacity] at target
  rw [Listing4EntryLayout.forms,StringWrites.owned_run_append,bootRun]
  exact ⟨boot,target⟩

end SmcTuring.Appendix.Listing4TargetWrites

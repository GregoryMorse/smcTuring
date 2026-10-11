module
public import SmcTuring.Appendix.Listing4TargetTrace

public section
namespace SmcTuring.Appendix.Listing4EntryLayout
open Native Listing4StackLayout Listing4JumpLayout
@[expose] def size : Mode → Nat | .x86 => 52 | .x64 => 97
@[expose] def mainPC (mode : Mode) (start : Nat) := start+size mode
@[expose] def bytes (mode : Mode) (start : Nat) := Listing4Boot.bytes mode start++Listing4TargetLayout.bytes mode start (beginPC mode start)
@[expose] def forms (mode : Mode) (start : Nat) := Listing4Boot.forms mode start++Listing4TargetLayout.forms mode start (beginPC mode start)
theorem bytes_length (mode : Mode) (start : Nat) : (bytes mode start).length=size mode := by
  rw [bytes,List.length_append,Listing4Boot.bytes_length,Listing4TargetLayout.bytes_length];cases mode <;> rfl
theorem endpoint (mode : Mode) (start : Nat) : Listing4TargetLayout.endPC mode (beginPC mode start)=mainPC mode start := by
  rw [(Listing4TargetLayout.positions mode _).2.2.2,Listing4Boot.endpoint]
  cases mode <;> dsimp [mainPC,size,Listing4Boot.size,Listing4TargetLayout.size] <;> omega
theorem instruction_count (mode : Mode) (start : Nat) : (forms mode start).length=(if mode=.x86 then 8 else 13) := by cases mode <;> rfl
theorem begin_ranges (mode : Mode) (start : Nat) : Listing4TargetLayout.Ranges mode start (beginPC mode start) := by
  cases mode with
  | x86 => constructor <;> intro impossible <;> cases impossible
  | x64 =>
    constructor <;> intro _ <;>
      dsimp [beginPC,callPC,jumpPC,Listing4StackLayout.size,prefixSize,stptr,returnField,
        Listing4TargetLayout.thirdPC,Listing4TargetLayout.fourthPC,Listing4TargetLayout.fifthPC,Listing4TargetLayout.endPC,
        StackMemory.size,wordPrefix,Listing4TargetLayout.adjustSize,WordAddImmediate.length] <;>
      unfold Relocation.SignedDelta Relocation.delta <;> omega
theorem target_after_stack (mode : Mode) (start : Nat) : start+Listing4StackLayout.size mode ≤ beginPC mode start := by
  dsimp [beginPC,callPC,jumpPC];omega
theorem stack_capacity (mode : Mode) (start : Nat) (fits : mainPC mode start<2^(8*mode.wordBytes)) :
    start+Listing4StackLayout.size mode<2^(8*mode.wordBytes) := by
  cases mode <;> dsimp [mainPC,size,Listing4StackLayout.size] at * <;> omega
theorem boot_capacity (mode : Mode) (start : Nat) (fits : mainPC mode start<2^(8*mode.wordBytes)) :
    start+Listing4Boot.size mode<2^(8*mode.wordBytes) := by
  cases mode <;> dsimp [mainPC,size,Listing4Boot.size] at * <;> omega
theorem target_capacity (mode : Mode) (start : Nat) (fits : mainPC mode start<2^(8*mode.wordBytes)) :
    beginPC mode start+Listing4TargetLayout.size mode<2^(8*mode.wordBytes) := by
  have endpoint:=endpoint mode start
  rw [(Listing4TargetLayout.positions mode _).2.2.2] at endpoint
  rw [endpoint];exact fits
end SmcTuring.Appendix.Listing4EntryLayout

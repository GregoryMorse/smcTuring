module
public import SmcTuring.Appendix.Listing4BootValues
public import SmcTuring.Native.StackAdjust

public section
namespace SmcTuring.Appendix.Listing4TargetLayout
open Native LittleEndian Listing4StackLayout
@[expose] def first (mode : Mode) (start target : Nat) := StackMemory.form mode .exchangeStack target (stptr mode start)
@[expose] def adjustSize (mode : Mode) := WordAddImmediate.length mode
@[expose] def adjust (mode : Mode) (start target : Nat) : StringStack.Form mode :=
  match mode with
  | .x86 => .addSmall (Relocation.memoryDisp .x86 (target+6+7) (stptr .x86 start)) 4
  | .x64 => StackAdjust.subtract .x64 (target+7) (stptr .x64 start) 10
@[expose] def thirdPC (mode : Mode) (target : Nat) := target+StackMemory.size mode+adjustSize mode
@[expose] def fourthPC (mode : Mode) (target : Nat) := thirdPC mode target+StackMemory.size mode
@[expose] def fifthPC (mode : Mode) (target : Nat) := fourthPC mode target+StackMemory.size mode
@[expose] def endPC (mode : Mode) (target : Nat) := fifthPC mode target+StackMemory.size mode
@[expose] def third (mode : Mode) (start target : Nat) : Native.Form mode :=
  WordMemoryArithmetic.form mode .exchange (thirdPC mode target) (stptr mode start)
@[expose] def fourth (mode : Mode) (start target : Nat) := StackMemory.form mode .storeAcc (fourthPC mode target) (returnField mode start)
@[expose] def fifth (mode : Mode) (start target : Nat) : Native.Form mode :=
  WordMemoryArithmetic.form mode .exchange (fifthPC mode target) (stptr mode start)
@[expose] def adjustBytes (mode : Mode) (start target : Nat) : List Byte :=
  match mode with
  | .x86 => WordAddImmediate.encode .x86 (Relocation.memoryDisp .x86 (target+6+7) (stptr .x86 start)) 4
  | .x64 => StringForm.encode .x64 (StringOperands.subtract .x64 (target+7) (stptr .x64 start) 10)
@[expose] def bytes (mode : Mode) (start target : Nat) :=
  Native.encode mode (first mode start target)++adjustBytes mode start target++Native.encode mode (third mode start target)++
    Native.encode mode (fourth mode start target)++Native.encode mode (fifth mode start target)
@[expose] def forms (mode : Mode) (start target : Nat) : List (StringStack.Form mode) :=
  [StringStack.native mode (first mode start target),adjust mode start target,StringStack.native mode (third mode start target),
    StringStack.native mode (fourth mode start target),StringStack.native mode (fifth mode start target)]
@[expose] def size : Mode → Nat | .x86 => 31 | .x64 => 36
theorem positions (mode : Mode) (target : Nat) :
    thirdPC mode target=target+(if mode=.x86 then 13 else 15) ∧
    fourthPC mode target=target+(if mode=.x86 then 19 else 22) ∧
    fifthPC mode target=target+(if mode=.x86 then 25 else 29) ∧
    endPC mode target=target+size mode := by
  cases mode <;> dsimp [thirdPC,fourthPC,fifthPC,endPC,StackMemory.size,adjustSize,WordAddImmediate.length,wordPrefix,size] <;> omega
theorem bytes_length (mode : Mode) (start target : Nat) : (bytes mode start target).length = size mode := by
  cases mode <;> rfl
theorem instruction_count (mode : Mode) (start target : Nat) : (forms mode start target).length=5 := rfl
theorem first_length (mode : Mode) (start target : Nat) : (Native.encode mode (first mode start target)).length=StackMemory.size mode := by cases mode <;> rfl
theorem adjust_length (mode : Mode) (start target : Nat) : (adjustBytes mode start target).length=adjustSize mode := by cases mode <;> rfl
theorem third_length (mode : Mode) (start target : Nat) : (Native.encode mode (third mode start target)).length=StackMemory.size mode := by cases mode <;> rfl
theorem fourth_length (mode : Mode) (start target : Nat) : (Native.encode mode (fourth mode start target)).length=StackMemory.size mode := by cases mode <;> rfl
theorem fifth_length (mode : Mode) (start target : Nat) : (Native.encode mode (fifth mode start target)).length=StackMemory.size mode := by cases mode <;> rfl
theorem slot_adjustment (mode : Mode) (start : Nat) :
    (match mode with
      | .x86 => Arithmetic.encodeNat .x86 (returnField .x86 start)+Arithmetic.encodeNat .x86 4
      | .x64 => Arithmetic.encodeNat .x64 (returnField .x64 start)-Arithmetic.encodeNat .x64 10) =
      Arithmetic.encodeNat mode (stptr mode start) := by
  cases mode with
  | x86 =>
    change BitVec.ofNat 32 (returnField .x86 start)+BitVec.ofNat 32 4 = BitVec.ofNat 32 (stptr .x86 start)
    rw [BitVec.ofNat_add_ofNat];congr 1
  | x64 =>
    have above : Arithmetic.encodeNat .x64 (returnField .x64 start)=Arithmetic.encodeNat .x64 (stptr .x64 start)+Arithmetic.encodeNat .x64 10 := by
      change BitVec.ofNat 64 (returnField .x64 start)=BitVec.ofNat 64 (stptr .x64 start)+BitVec.ofNat 64 10
      rw [BitVec.ofNat_add_ofNat];congr 1
    rw [above,BitVec.add_sub_cancel]

structure Ranges (mode : Mode) (start target : Nat) : Prop where
  first : mode=.x64 → Relocation.SignedDelta (target+StackMemory.size mode) (stptr mode start)
  adjust : mode=.x64 → Relocation.SignedDelta (thirdPC mode target) (stptr mode start)
  third : mode=.x64 → Relocation.SignedDelta (fourthPC mode target) (stptr mode start)
  fourth : mode=.x64 → Relocation.SignedDelta (fifthPC mode target) (returnField mode start)
  fifth : mode=.x64 → Relocation.SignedDelta (endPC mode target) (stptr mode start)
end SmcTuring.Appendix.Listing4TargetLayout

module
public import SmcTuring.Appendix.Listing4StackInitTrace

public section
namespace SmcTuring.Appendix.Listing4JumpLayout
open Native LittleEndian Listing4StackLayout
@[expose] def prefixSize : Mode → Nat | .x86 => 6 | .x64 => 22
@[expose] def jumpPC (mode : Mode) (start : Nat) := start+size mode
@[expose] def callPC (mode : Mode) (start : Nat) := jumpPC mode start+prefixSize mode
@[expose] def beginPC (mode : Mode) (start : Nat) := callPC mode start+5
@[expose] def exchange (mode : Mode) (start : Nat) : Native.Form mode :=
  StackMemory.form mode .exchangeStack (jumpPC mode start) (stptr mode start)
@[expose] def adjust (start : Nat) : StringStack.Form .x64 :=
  .addSmall (Relocation.memoryDisp .x64 (jumpPC .x64 start+7+8) (returnField .x64 start)) 18
@[expose] def exchangeSaved (start : Nat) : Native.Form .x64 :=
  StackMemory.form .x64 .exchangeStack (jumpPC .x64 start+7+8) (returnField .x64 start)
@[expose] def prefixBytes (mode : Mode) (start : Nat) : List Byte :=
  match mode with
  | .x86 => Native.encode .x86 (exchange .x86 start)
  | .x64 => Native.encode .x64 (exchange .x64 start) ++
      WordAddImmediate.encode .x64 (Relocation.memoryDisp .x64 (jumpPC .x64 start+7+8) (returnField .x64 start)) 18 ++
      Native.encode .x64 (exchangeSaved start)
@[expose] def call (mode : Mode) : Native.Form mode := .callRelative 0
@[expose] def bytes (mode : Mode) (start : Nat) : List Byte  := prefixBytes mode start++Native.encode mode (call mode)
@[expose] def prefixForms (mode : Mode) (start : Nat) : List (StringStack.Form mode) :=
  match mode with
  | .x86 => [StringStack.native .x86 (exchange .x86 start)]
  | .x64 => [StringStack.native .x64 (exchange .x64 start),adjust start,StringStack.native .x64 (exchangeSaved start)]
@[expose] def forms (mode : Mode) (start : Nat) := prefixForms mode start++[StringStack.native mode (call mode)]
@[expose] def callTop (mode : Mode) (start : Nat) : Word mode :=
  match mode with
  | .x86 => Arithmetic.encodeNat .x86 (stptr .x86 start)
  | .x64 => Arithmetic.encodeNat .x64 (stptr .x64 start)+Arithmetic.encodeNat .x64 18

theorem prefix_length (mode : Mode) (start : Nat) : (prefixBytes mode start).length = prefixSize mode := by cases mode <;> rfl
theorem bytes_length (mode : Mode) (start : Nat) : (bytes mode start).length = prefixSize mode+5 := by cases mode <;> rfl
theorem positions (mode : Mode) (start : Nat) :
    jumpPC mode start=start+(if mode=.x86 then 10 else 34) ∧
    callPC mode start=start+(if mode=.x86 then 16 else 56) ∧
    beginPC mode start=start+(if mode=.x86 then 21 else 61) := by cases mode <;> dsimp [jumpPC,callPC,beginPC,size,prefixSize] <;> omega
theorem first_reach (mode : Mode) (start : Nat) :
    mode=.x64 → Relocation.SignedDelta (jumpPC mode start+StackMemory.size mode) (stptr mode start) := by
  intro only;subst mode
  dsimp [jumpPC,StackMemory.size,wordPrefix,stptr,size]
  unfold Relocation.SignedDelta Relocation.delta;omega
theorem adjust_reach (start : Nat) : Relocation.SignedDelta (jumpPC .x64 start+7+8) (returnField .x64 start) := by
  dsimp [jumpPC,size,returnField];unfold Relocation.SignedDelta Relocation.delta;omega
theorem saved_reach (start : Nat) :
    Relocation.SignedDelta (jumpPC .x64 start+7+8+7) (returnField .x64 start) := by
  dsimp [jumpPC,size,returnField];unfold Relocation.SignedDelta Relocation.delta;omega
theorem stack_decrement (mode : Mode) (start : Nat) :
    callTop mode start-Arithmetic.encodeNat mode mode.wordBytes = Arithmetic.encodeNat mode (returnField mode start) := by
  have value : callTop mode start = Arithmetic.encodeNat mode (returnField mode start)+Arithmetic.encodeNat mode mode.wordBytes := by
    cases mode with
    | x86 =>
      change BitVec.ofNat 32 (stptr .x86 start) = BitVec.ofNat 32 (returnField .x86 start)+BitVec.ofNat 32 4
      rw [BitVec.ofNat_add_ofNat]
      congr 1
    | x64 =>
      change BitVec.ofNat 64 (stptr .x64 start)+BitVec.ofNat 64 18 = BitVec.ofNat 64 (returnField .x64 start)+BitVec.ofNat 64 8
      rw [BitVec.ofNat_add_ofNat,BitVec.ofNat_add_ofNat]
      congr 1
  rw [value,BitVec.add_sub_cancel]
end SmcTuring.Appendix.Listing4JumpLayout

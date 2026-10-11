module
public import SmcTuring.Appendix.Listing8StackMetadata

public section
namespace SmcTuring.Appendix.Listing8JumpLayout
open Native LittleEndian Listing4StackLayout
@[expose] def jumpPC (mode : Mode) (origin : Nat) := origin+(if mode=.x86 then 795 else 1247)
@[expose] def callPC (mode : Mode) (origin : Nat) := jumpPC mode origin+Listing4JumpLayout.prefixSize mode
@[expose] def failPC (mode : Mode) (origin : Nat) := callPC mode origin+5
@[expose] def exchange (mode : Mode) (origin : Nat) := StackMemory.form mode .exchangeStack (jumpPC mode origin) (stptr mode origin)
@[expose] def adjust (origin : Nat) : StringStack.Form .x64 :=
  .addSmall (Relocation.memoryDisp .x64 (jumpPC .x64 origin+7+8) (returnField .x64 origin)) 18
@[expose] def exchangeSaved (origin : Nat) :=
  StackMemory.form .x64 .exchangeStack (jumpPC .x64 origin+7+8) (returnField .x64 origin)
@[expose] def prefixBytes (mode : Mode) (origin : Nat) : List Byte :=
  match mode with
  | .x86 => Native.encode .x86 (exchange .x86 origin)
  | .x64 => Native.encode .x64 (exchange .x64 origin) ++
      WordAddImmediate.encode .x64 (Relocation.memoryDisp .x64 (jumpPC .x64 origin+7+8) (returnField .x64 origin)) 18 ++
      Native.encode .x64 (exchangeSaved origin)
@[expose] def prefixForms (mode : Mode) (origin : Nat) : List (StringStack.Form mode) :=
  match mode with
  | .x86 => [StringStack.native .x86 (exchange .x86 origin)]
  | .x64 => [StringStack.native .x64 (exchange .x64 origin),adjust origin,StringStack.native .x64 (exchangeSaved origin)]
@[expose] def call (mode : Mode) (origin : Nat) (failed : Bool) : Native.Form mode :=
  .callRelative (if failed then 0 else Relocation.relative32 (failPC mode origin) (Listing8BootImage.beginPC mode origin))
@[expose] def forms (mode : Mode) (origin : Nat) (failed : Bool) :=
  prefixForms mode origin++[StringStack.native mode (call mode origin failed)]
theorem prefix_length (mode : Mode) (origin : Nat) : (prefixBytes mode origin).length=Listing4JumpLayout.prefixSize mode := by cases mode <;> rfl
theorem instruction_count (mode : Mode) (origin : Nat) (failed : Bool) : (forms mode origin failed).length=(if mode=.x86 then 2 else 4) := by cases mode <;> rfl
theorem positions (mode : Mode) (origin : Nat) :
    callPC mode origin=origin+(if mode=.x86 then 801 else 1269) ∧
    failPC mode origin=origin+(if mode=.x86 then 806 else 1274) := by
  cases mode <;> dsimp [callPC,failPC,jumpPC,Listing4JumpLayout.prefixSize] <;> omega
theorem first_reach (mode : Mode) (origin : Nat) :
    mode=.x64 → Relocation.SignedDelta (jumpPC mode origin+StackMemory.size mode) (stptr mode origin) := by
  intro only;subst mode
  dsimp [jumpPC,StackMemory.size,wordPrefix,stptr]
  unfold Relocation.SignedDelta Relocation.delta;omega
theorem adjust_reach (origin : Nat) : Relocation.SignedDelta (jumpPC .x64 origin+7+8) (returnField .x64 origin) := by
  dsimp [jumpPC,returnField];unfold Relocation.SignedDelta Relocation.delta;omega
theorem saved_reach (origin : Nat) : Relocation.SignedDelta (jumpPC .x64 origin+7+8+7) (returnField .x64 origin) := by
  dsimp [jumpPC,returnField];unfold Relocation.SignedDelta Relocation.delta;omega
theorem backedge_reach (mode : Mode) (origin : Nat) :
    Relocation.SignedDelta (failPC mode origin) (Listing8BootImage.beginPC mode origin) := by
  rw [(positions mode origin).2]
  have begin:=(Listing4JumpLayout.positions mode origin).2.2
  change Listing8BootImage.beginPC mode origin=_ at begin
  rw [begin]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> unfold Relocation.SignedDelta Relocation.delta <;> omega
theorem slots_before (mode : Mode) (origin : Nat) :
    stptr mode origin+mode.wordBytes ≤ jumpPC mode origin ∧
    returnField mode origin+mode.wordBytes ≤ jumpPC mode origin := by
  cases mode <;> dsimp [stptr,returnField,jumpPC,Mode.wordBytes] <;> omega
theorem stack_capacity (mode : Mode) (origin : Nat) (capacity : failPC mode origin<2^(8*mode.wordBytes)) :
    origin+Listing4StackLayout.size mode<2^(8*mode.wordBytes) := by
  have coords:=(positions mode origin).2
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> dsimp [Listing4StackLayout.size] <;> omega
end SmcTuring.Appendix.Listing8JumpLayout

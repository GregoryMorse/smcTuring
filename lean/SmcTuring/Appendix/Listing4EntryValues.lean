module
public import SmcTuring.Appendix.Listing4Entry

public section
namespace SmcTuring.Appendix.Listing4EntryValues
open Native Listing4StackLayout
theorem target_carry_clear (mode : Mode) (start : Nat)
    (fits : Listing4EntryLayout.mainPC mode start<2^(8*mode.wordBytes)) :
    Listing4TargetEffects.flag mode start=false := by
  cases mode with
  | x86 =>
    change start+52<2^32 at fits
    have fieldFits : returnField .x86 start<2^32 := by dsimp [returnField];omega
    change decide ((BitVec.ofNat 32 (returnField .x86 start)).toNat+(BitVec.ofNat 32 4).toNat ≥ 2^32)=false
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fieldFits,Nat.mod_eq_of_lt (by decide : 4<2^32)]
    apply decide_eq_false
    dsimp [returnField];omega
  | x64 =>
    change start+97<2^64 at fits
    have fieldFits : returnField .x64 start<2^64 := by dsimp [returnField];omega
    change decide ((BitVec.ofNat 64 (returnField .x64 start)).toNat<(BitVec.ofNat 64 10).toNat)=false
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fieldFits,Nat.mod_eq_of_lt (by decide : 10<2^64)]
    apply decide_eq_false
    dsimp [returnField];omega

theorem stptr_value (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : Listing4EntryLayout.mainPC mode start<2^(8*mode.wordBytes)) :
    MixedMemory.getWord mode (Listing4Entry.finish mode start seed).principal.memory (stptr mode start)=
      Arithmetic.encodeNat mode (stptr mode start) := by
  rw [Listing4Entry.memory mode start seed fits]
  exact initial_stptr mode start _ (Listing4EntryLayout.stack_capacity mode start fits) (Listing4Entry.stack_current mode start seed)
theorem return_value (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : Listing4EntryLayout.mainPC mode start<2^(8*mode.wordBytes)) :
    MixedMemory.getWord mode (Listing4Entry.finish mode start seed).principal.memory (returnField mode start)=
      Arithmetic.encodeNat mode (stptr mode start) := by
  rw [Listing4Entry.memory mode start seed fits]
  exact Listing4TargetMemory.original_return mode start _ (Listing4EntryLayout.stack_capacity mode start fits) (Listing4Entry.stack_current mode start seed)
theorem code_current (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : Listing4EntryLayout.mainPC mode start<2^(8*mode.wordBytes)) :
    ByteMemory.bytesAt (Listing4Entry.finish mode start seed).principal.memory start (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode start := by
  rw [Listing4Entry.memory mode start seed fits]
  exact Listing4Entry.initial_current mode start seed
end SmcTuring.Appendix.Listing4EntryValues

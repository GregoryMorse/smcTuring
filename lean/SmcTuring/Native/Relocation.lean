module
public import SmcTuring.Native.Execution

public section

namespace SmcTuring.Native.Relocation

open Execution

@[expose] def delta (next target : Nat) : Int := (target : Int) - (next : Int)
@[expose] def SignedDelta (next target : Nat) : Prop :=
  And (-2 ^ (31 : Nat) <= delta next target) (delta next target < 2 ^ (31 : Nat))

/-- COFF rel32 payload, including backward transfers. The range condition
below is explicit; silently truncating an out-of-range relocation is excluded. -/
@[expose] def relative32 (next target : Nat) : BitVec 32 := BitVec.ofInt 32 (delta next target)

@[expose] def memoryDisp (mode : Mode) (next target : Nat) : BitVec 32 :=
  match mode with | .x86 => BitVec.ofNat 32 target | .x64 => relative32 next target

theorem relative32_toInt (next target : Nat) (fits : SignedDelta next target) :
    (relative32 next target).toInt = delta next target :=
  BitVec.toInt_ofInt_eq_self (by decide) fits.1 fits.2

theorem sign_extended_relative32 (next target : Nat) (fits : SignedDelta next target) :
    (relative32 next target).signExtend 64 = BitVec.ofInt 64 (delta next target) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), relative32_toInt next target fits]
  exact (BitVec.toInt_ofInt_eq_self (by decide)
    (by have low := fits.1; omega) (by have high := fits.2; omega)).symm

/-- Relative address arithmetic reaches the target in either IP width. The
natural-address/canonical-address conditions are separate from this word law. -/
theorem add_relative32 (mode : Mode) (next target : Nat) (fits : SignedDelta next target) :
    Arithmetic.encodeNat mode next + displacementWord mode (relative32 next target) = Arithmetic.encodeNat mode target := by
  have sum : (next : Int) + delta next target = (target : Int) := by unfold delta; omega
  cases mode with
  | x86 =>
    change BitVec.ofNat 32 next + BitVec.ofInt 32 (delta next target) = BitVec.ofNat 32 target
    rw [<-BitVec.ofInt_natCast 32 next, <-BitVec.ofInt_add, sum, BitVec.ofInt_natCast]
  | x64 =>
    change BitVec.add (BitVec.ofNat 64 next) ((relative32 next target).signExtend 64) = BitVec.ofNat 64 target
    rw [sign_extended_relative32 next target fits]
    change BitVec.ofNat 64 next + BitVec.ofInt 64 (delta next target) = BitVec.ofNat 64 target
    rw [<-BitVec.ofInt_natCast 64 next, <-BitVec.ofInt_add, sum, BitVec.ofInt_natCast]

theorem memory_hits (mode : Mode) (next target : Nat)
    (fits : mode = .x64 -> SignedDelta next target) :
    memoryAddress mode (Arithmetic.encodeNat mode next) (memoryDisp mode next target) = Arithmetic.encodeNat mode target := by
  cases mode with
  | x86 => rfl
  | x64 => exact add_relative32 .x64 next target (fits rfl)

theorem next_pc (mode : Mode) (state : State mode) (form : Form mode) (pc : Nat)
    (location : state.pc = Arithmetic.encodeNat mode pc) :
    nextPC mode form state = Arithmetic.encodeNat mode (pc + instructionLength mode form) := by
  unfold nextPC
  rw [location]
  exact BitVec.ofNat_add_ofNat pc (instructionLength mode form)

theorem memory_length (mode : Mode) (operation : MemoryOp) (displacement : BitVec 32) :
    instructionLength mode (.memory operation displacement) = instructionLength mode (.memory operation 0) := by
  cases mode <;> cases operation <;> rfl

/-- Resolution uses the complete instruction size, including SBB's imm8 zero.
It therefore covers the distinct COFF REL32_1 case without using next-header IP. -/
@[expose] def instructionDisp (mode : Mode) (operation : MemoryOp) (pc target : Nat) : BitVec 32 :=
  memoryDisp mode (pc + instructionLength mode (.memory operation 0)) target

theorem instruction_memory_hits (mode : Mode) (operation : MemoryOp) (pc target : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (fits : mode = .x64 -> SignedDelta (pc + instructionLength mode (.memory operation 0)) target) :
    memoryAddress mode (nextPC mode (.memory operation (instructionDisp mode operation pc target)) state)
      (instructionDisp mode operation pc target) = Arithmetic.encodeNat mode target := by
  rw [next_pc mode state _ pc location, memory_length]
  exact memory_hits mode _ target fits

theorem relative_call_pc (mode : Mode) (pc target : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc) (fits : SignedDelta (pc + 5) target) :
    (execute mode (.callRelative (relative32 (pc + 5) target)) state).pc = Arithmetic.encodeNat mode target := by
  change nextPC mode (.callRelative (relative32 (pc + 5) target)) state +
    displacementWord mode (relative32 (pc + 5) target) = _
  rw [next_pc mode state _ pc location]
  exact add_relative32 mode (pc + 5) target fits

theorem relative_call_position (mode : Mode) (pc target : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode pc) (fits : SignedDelta (pc + 5) target)
    (targetFits : target < 2 ^ (8 * mode.wordBytes)) :
    (execute mode (.callRelative (relative32 (pc + 5) target)) state).pc.toNat = target := by
  rw [relative_call_pc mode pc target state location fits, Arithmetic.encode_nat_toNat mode target targetFits]

end SmcTuring.Native.Relocation

module
public import SmcTuring.Native.DwordArithmetic
public import SmcTuring.Appendix.InputOperand
public import SmcTuring.Appendix.DwordComparison

public section
namespace SmcTuring.Appendix.InputSelection
open Native Native.DwordCode
abbrev Dword := BitVec 32
@[expose] def difference (old fresh : Dword) (chosen : Bool) : Dword :=
  (old ^^^ fresh) &&& BranchAlgebra.mask chosen

theorem chosen_difference (old fresh : Dword) (chosen : Bool) :
    difference old fresh chosen = if chosen then old ^^^ fresh else 0 := by
  unfold difference
  rw [BitVec.and_comm,BranchAlgebra.and_mask]

theorem selected_symbol (old fresh : Dword) (chosen : Bool) :
    old ^^^ difference old fresh chosen = if chosen then fresh else old := by
  rw [chosen_difference]
  cases chosen <;> simp [←BitVec.xor_assoc]

theorem current_patch (memory : ByteMemory.Memory) (pc : Nat) (old fresh : Dword)
    (current : ByteMemory.bytesAt memory pc 7 = DwordArithmetic.encode (.xorAtAccumulator old)) :
    ByteMemory.bytesAt (put memory (pc+3) fresh) pc 7 =
      DwordArithmetic.encode (.xorAtAccumulator fresh) := by
  have back : ByteMemory.putBytes memory pc (DwordArithmetic.encode (.xorAtAccumulator old)) = memory :=
    ByteMemory.put_current _ _ _ current
  rw [←back,DwordArithmetic.base_xor_patch]
  exact ByteMemory.bytes_at_put _ _ _

theorem xor_then_and (memory : ByteMemory.Memory) (pc : Nat) (old fresh : Dword) (chosen : Bool)
    (current : ByteMemory.bytesAt memory pc 7 = DwordArithmetic.encode (.xorAtAccumulator old)) :
    ByteMemory.bytesAt
      (put (put memory (pc+3) (old ^^^ fresh)) (pc+3) (difference old fresh chosen)) pc 7 =
      DwordArithmetic.encode (.xorAtAccumulator (difference old fresh chosen)) := by
  rw [put_overwrite]
  exact current_patch memory pc old _ current

theorem tape_target (mode : Mode) (state : Execution.State mode) (head : Nat)
    (cursor : state.accumulator = Arithmetic.encodeNat mode head) (value : Dword) :
    DwordArithmetic.address mode (.xorAtAccumulator value) state = Arithmetic.encodeNat mode (head+6) := by
  change state.accumulator + Arithmetic.encodeNat mode 6 = _
  rw [cursor]
  exact BitVec.ofNat_add_ofNat head 6

theorem tape_effect (mode : Mode) (state : Execution.State mode) (head : Nat) (old fresh : Dword) (chosen : Bool)
    (cursor : state.accumulator = Arithmetic.encodeNat mode head)
    (fits : head+6 < 2^(8*mode.wordBytes)) (tape : get state.memory (head+6) = old) :
    DwordArithmetic.execute mode (.xorAtAccumulator (difference old fresh chosen)) state =
      { state with
        pc := state.pc + Arithmetic.encodeNat mode 7
        carry := false
        memory := put state.memory (head+6) (if chosen then fresh else old) } := by
  unfold DwordArithmetic.execute DwordArithmetic.value DwordArithmetic.carry DwordArithmetic.prior
  rw [tape_target mode state head cursor,Arithmetic.encode_nat_toNat mode _ fits,tape]
  rw [DwordArithmetic.result,selected_symbol]
  rfl

/-- The final base-addressed XOR is fetched from the actual selected immediate.
Full-width cursor exchange/restoration belongs to the surrounding caller. -/
theorem tape_step (mode : Mode) (state : Execution.State mode) (head : Nat) (old fresh : Dword) (chosen : Bool)
    (cursor : state.accumulator = Arithmetic.encodeNat mode head)
    (fits : head+6 < 2^(8*mode.wordBytes)) (tape : get state.memory (head+6) = old)
    (current : ByteMemory.bytesAt state.memory state.pc.toNat 7 =
      DwordArithmetic.encode (.xorAtAccumulator (difference old fresh chosen))) :
    DwordArithmetic.step mode state =
      some { state with
        pc := state.pc + Arithmetic.encodeNat mode 7
        carry := false
        memory := put state.memory (head+6) (if chosen then fresh else old) } := by
  rw [DwordArithmetic.step_encoding mode state (.xorAtAccumulator (difference old fresh chosen)) current,tape_effect mode state head old fresh chosen cursor fits tape]

theorem tape_code_frame (mode : Mode) (state : Execution.State mode) (head : Nat)
    (old fresh : Dword) (chosen : Bool) (cursor : state.accumulator = Arithmetic.encodeNat mode head)
    (fits : head+6 < 2^(8*mode.wordBytes)) (tape : get state.memory (head+6) = old)
    (position : Nat) (outside : ¬ByteMemory.Inside (head+6) 4 position) :
    (DwordArithmetic.execute mode (.xorAtAccumulator (difference old fresh chosen)) state).memory position =
      state.memory position := by
  rw [tape_effect mode state head old fresh chosen cursor fits tape]
  exact ByteMemory.put_frame _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using outside)

theorem tape_owned_write (mode : Mode) (state : Execution.State mode) (head : Nat)
    (old fresh : Dword) (chosen : Bool) (cursor : state.accumulator = Arithmetic.encodeNat mode head)
    (fits : head+6 < 2^(8*mode.wordBytes)) (owned : Nat → Prop) (fieldOwned : owned (head+6)) :
    owned (DwordArithmetic.address mode (.xorAtAccumulator (difference old fresh chosen)) state).toNat ∧
    ByteMemory.Inside (head+6) 4 (head+6) := by
  rw [tape_target mode state head cursor,Arithmetic.encode_nat_toNat mode _ fits]
  exact ⟨fieldOwned,by unfold ByteMemory.Inside; omega⟩

theorem comparison_selection (mode : Mode) (layout : DwordComparison.Layout)
    (symbol fresh : Dword) (state : Execution.State mode) :
    symbol ^^^ ((symbol ^^^ fresh) &&& get (DwordComparison.finish mode layout symbol state).memory layout.mask) =
      if DwordComparison.candidate layout state = symbol then fresh else symbol := by
  rw [DwordComparison.mask_value mode layout symbol state]
  by_cases equal : DwordComparison.candidate layout state = symbol
  · simp only [ite_eq_left equal]
    change symbol ^^^ ((symbol ^^^ fresh) &&& BitVec.allOnes 32) = fresh
    rw [BitVec.and_allOnes,←BitVec.xor_assoc]
    simp
  · simp [equal]

end SmcTuring.Appendix.InputSelection

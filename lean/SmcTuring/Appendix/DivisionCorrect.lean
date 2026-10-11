module
public import SmcTuring.Appendix.DivisionObservations

public section
namespace SmcTuring.Appendix.DivisionCorrect
open DivisionControl DivisionBlocks DivisionExecution
attribute [local irreducible] DivisionControl.run DivisionWords.run DivisionExecution.loop

@[expose] def expected (layout : Layout) (initial : State) : Word :=
  let x := initial.data.memory (layout.fields .x)
  let y := initial.data.memory (layout.fields .y)
  if layout.signed then DivisionSignedAlgebra.result layout.mod x y
  else if layout.mod then x.umod y else x.udiv y

@[expose] def expectedCarry (layout : Layout) (initial : State) : Bool :=
  let x := initial.data.memory (layout.fields .x)
  let y := initial.data.memory (layout.fields .y)
  if layout.signed then
    DivisionSignedAlgebra.negative layout.mod x y &&
      decide (0 < (BitVec.ofNat 32 (DivisionSignedAlgebra.magnitudeResult layout.mod x y)).toNat ∧
        (BitVec.ofNat 32 (DivisionSignedAlgebra.magnitudeResult layout.mod x y)).toNat < 2147483648)
  else false

theorem selected (layout : Layout) (initial final : State)
    (nonzero : initial.data.memory (layout.fields .y) ≠ 0)
    (post : Post layout
      (DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .x)))
      (DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .y))) initial final) :
    DivisionStages.selectedResult layout.fields layout.mod final.data =
      BitVec.ofNat 32
        (if layout.mod then (DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .x))).toNat %
          (DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .y))).toNat
        else (DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .x))).toNat /
          (DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .y))).toNat) := by
  let dividend := DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .x))
  let divisor := DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .y))
  have denominator : divisor ≠ 0 := DivisionDataCorrect.divisor_nonzero _ _ nonzero
  have arithmetic := DivisionAlgebra.full_word_division dividend divisor denominator
  have low := post.invariant.2.2.1
  have high := post.invariant.2.2.2.1
  simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one, DivisionPacked.packed,
    Nat.mod_one, zero_mul, zero_add] at low high
  rw [arithmetic.1] at low
  rw [arithmetic.2] at high
  apply BitVec.eq_of_toNat_eq
  cases mod : layout.mod with
  | false =>
      simp only [DivisionStages.selectedResult, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (DivisionAlgebra.quotient_fits dividend divisor)]
      exact low
  | true =>
      simp only [DivisionStages.selectedResult, ite_true, BitVec.toNat_ofNat]
      have bound : dividend.toNat % divisor.toNat < 4294967296 :=
        lt_of_le_of_lt (Nat.mod_le _ _) dividend.isLt
      rw [Nat.mod_eq_of_lt bound]
      exact high

theorem output (layout : Layout) (initial final : State) (commands : List Instruction)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address initial)
    (trace : divide layout initial = some (commands, final))
    (nonzero : initial.data.memory (layout.fields .y) ≠ 0)
    (post : Post layout
      (DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .x)))
      (DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .y))) initial final) :
    final.data.memory (layout.fields .result) = expected layout initial := by
  rw [post.output]
  cases signed : layout.signed with
  | false =>
      simp only [DivisionStages.finishValue, signed, Bool.false_eq_true, ite_false,
        selected layout initial final nonzero post, DivisionDataCorrect.argument, expected]
      cases mod : layout.mod
      · simpa only [mod, Bool.false_eq_true, ite_false] using
          DivisionSignedAlgebra.quotient_word (initial.data.memory (layout.fields .x)) (initial.data.memory (layout.fields .y))
      · simpa only [mod, ite_true] using
          DivisionSignedAlgebra.remainder_word (initial.data.memory (layout.fields .x)) (initial.data.memory (layout.fields .y))
  | true =>
      have sign := DivisionObservations.divide_sign layout initial separate ready commands final trace signed
      simp only [DivisionStages.finishValue, signed, ite_true, sign,
        selected layout initial final nonzero post, DivisionDataCorrect.argument,
        expected, DivisionSignedAlgebra.result, DivisionSignedAlgebra.applySign,
        DivisionSignedAlgebra.magnitudeResult]
      rw [BitVec.and_comm]

theorem carry (layout : Layout) (initial final : State) (commands : List Instruction)
    (separate : Separate layout) (ready : StackReady layout.pointer layout.address initial)
    (trace : divide layout initial = some (commands, final))
    (nonzero : initial.data.memory (layout.fields .y) ≠ 0)
    (post : Post layout
      (DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .x)))
      (DivisionDataCorrect.argument layout.signed (initial.data.memory (layout.fields .y))) initial final) :
    final.data.carry = expectedCarry layout initial := by
  rw [post.carry]
  cases signed : layout.signed with
  | false => simp [expectedCarry, signed]
  | true =>
      have sign := DivisionObservations.divide_sign layout initial separate ready commands final trace signed
      simp only [ite_true, sign]
      rw [DivisionWordAlgebra.signed_result_carry, selected layout initial final nonzero post]
      simp only [expectedCarry, DivisionDataCorrect.argument, signed, ite_true,
        DivisionSignedAlgebra.magnitudeResult]
      rfl

structure Spec (layout : Layout) (initial final : State) : Prop where
  output : final.data.memory (layout.fields .result) = expected layout initial
  carry : final.data.carry = expectedCarry layout initial
  inputX : final.data.memory (layout.fields .x) = initial.data.memory (layout.fields .x)
  inputY : final.data.memory (layout.fields .y) = initial.data.memory (layout.fields .y)
  accumulator : final.data.accumulator = initial.data.accumulator
  stack : final.stack = initial.stack
  pc : final.pc = endPC layout
  ready : StackReady layout.pointer layout.address final
  displacement : final.data.memory (layout.fields .displacement) = 0
  frame : ∀ field, (∀ slot, field ≠ layout.fields slot) → final.data.memory field = initial.data.memory field

/-- The complete literal word/control proof is constructed from initial setup
and original operands. Physical bytes and ISA/coherent fetch are separate gates. -/
theorem correct (layout : Layout) (state : State) (separate : Separate layout)
    (ready : StackReady layout.pointer layout.address state)
    (entry : state.pc = layout.origin) (direct : state.data.memory layout.entryDisplacement = 0)
    (back : state.data.memory layout.backDisplacement = backDelta layout)
    (initial : state.data.memory (layout.fields .displacement) = 0)
    (nonzero : state.data.memory (layout.fields .y) ≠ 0)
    (codeField : Nat → Prop)
    (owned : ∀ block slot, slot ∈ written layout block → codeField (layout.fields slot))
    (pointerOwned : codeField layout.pointer) (addressOwned : codeField layout.address) :
    ∃ commands final, divide layout state = some (commands, final) ∧
      run commands state = final ∧ PureRun codeField commands state ∧ Spec layout state final := by
  obtain ⟨commands, final, trace, execution, post⟩ := divide_finishes layout state separate ready entry direct back initial nonzero
  have inputs := DivisionObservations.divide_inputs layout state separate ready commands final trace
  refine ⟨commands, final, trace, execution,
    DivisionObservations.divide_pure layout state separate ready commands final trace codeField owned pointerOwned addressOwned, ?_⟩
  exact ⟨output layout state final commands separate ready trace nonzero post,
    carry layout state final commands separate ready trace nonzero post, inputs.1, inputs.2,
    post.accumulator, post.stack, post.pc, post.ready, post.displacement,
    fun field outside => DivisionObservations.divide_frame layout state separate ready commands final trace field outside⟩

theorem signed_quotient (layout : Layout) (initial final : State)
    (spec : Spec layout initial final) (signed : layout.signed = true) (mod : layout.mod = false)
    (nonzero : initial.data.memory (layout.fields .y) ≠ 0)
    (noOverflow : ¬(initial.data.memory (layout.fields .x) = (2147483648 : Word) ∧
      initial.data.memory (layout.fields .y) = (-1 : Word))) :
    (final.data.memory (layout.fields .result)).toInt =
      (initial.data.memory (layout.fields .x)).toInt.tdiv (initial.data.memory (layout.fields .y)).toInt := by
  rw [spec.output]
  simp only [expected, signed, mod, ite_true]
  exact DivisionSignedAlgebra.quotient_toInt _ _ nonzero noOverflow

theorem signed_remainder (layout : Layout) (initial final : State)
    (spec : Spec layout initial final) (signed : layout.signed = true) (mod : layout.mod = true)
    (nonzero : initial.data.memory (layout.fields .y) ≠ 0) :
    (final.data.memory (layout.fields .result)).toInt =
      (initial.data.memory (layout.fields .x)).toInt.tmod (initial.data.memory (layout.fields .y)).toInt := by
  rw [spec.output]
  simp only [expected, signed, mod, ite_true]
  exact DivisionSignedAlgebra.remainder_toInt _ _ nonzero

theorem unsigned_quotient (layout : Layout) (initial final : State)
    (spec : Spec layout initial final) (signed : layout.signed = false) (mod : layout.mod = false) :
    final.data.memory (layout.fields .result) =
      (initial.data.memory (layout.fields .x)).udiv (initial.data.memory (layout.fields .y)) := by
  rw [spec.output]
  simp [expected, signed, mod]

theorem unsigned_remainder (layout : Layout) (initial final : State)
    (spec : Spec layout initial final) (signed : layout.signed = false) (mod : layout.mod = true) :
    final.data.memory (layout.fields .result) =
      (initial.data.memory (layout.fields .x)).umod (initial.data.memory (layout.fields .y)) := by
  rw [spec.output]
  simp [expected, signed, mod]

end SmcTuring.Appendix.DivisionCorrect

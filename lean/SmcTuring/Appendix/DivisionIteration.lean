module
public import SmcTuring.Appendix.DivisionStages
public import SmcTuring.Appendix.DivisionPacked

public section
namespace SmcTuring.Appendix.DivisionIteration
open Machine32 (Word State)
open DivisionWords DivisionPacked DivisionAlgebra

/-- This counts actual executions of the literal data body. Guard/CALL/byte
placement is added separately; it is not hidden in this definition. -/
@[expose] def iterate (fields : Fields) : Nat → State → State
  | 0, state => state
  | n + 1, state => run (body fields) (iterate fields n state)

@[expose] def Invariant (fields : Fields) (dividend divisor : Word) (k : Nat) (state : State) : Prop :=
  state.memory (fields .divisor) = divisor ∧
  state.memory (fields .divisor2) = divisor ∧
  (state.memory (fields .low)).toNat =
    packed dividend k (scan k (dividend.toNat / 2 ^ (32 - k)) divisor.toNat).quotient ∧
  (state.memory (fields .high)).toNat =
    (scan k (dividend.toNat / 2 ^ (32 - k)) divisor.toNat).remainder ∧
  state.memory (fields .counter) = BitVec.ofNat 32 (32 - k)

@[expose] def Ready (fields : Fields) (dividend divisor : Word) (state : State) : Prop :=
  state.memory (fields .divisor) = divisor ∧
  state.memory (fields .divisor2) = divisor ∧
  state.memory (fields .low) = dividend ∧
  state.memory (fields .high) = 0 ∧
  state.memory (fields .counter) = 32

theorem initial_invariant (fields : Fields) (dividend divisor : Word) (state : State)
    (ready : Ready fields dividend divisor state) :
    Invariant fields dividend divisor 0 state := by
  rcases ready with ⟨first, second, low, high, counter⟩
  simp [Invariant, first, second, low, high, counter, packed, scan,
    Nat.mod_eq_of_lt dividend.isLt]

theorem advance (fields : Fields) (dividend divisor : Word) (state : State) (k : Nat)
    (separate : Separate fields) (nonzero : 0 < divisor.toNat) (range : k < 32)
    (invariant : Invariant fields dividend divisor k state) :
    Invariant fields dividend divisor (k + 1) (run (body fields) state) := by
  rcases invariant with ⟨first, second, low, high, counter⟩
  have agrees : state.memory (fields .divisor2) = state.memory (fields .divisor) := by
    rw [first, second]
  have step := packed_step dividend (state.memory (fields .low))
    (state.memory (fields .high)) divisor k range nonzero low high
  have coordinate : 32 - (k + 1) = 31 - k := by omega
  have divisors := DivisionBody.body_divisor fields state separate
  refine ⟨divisors.1.trans first, divisors.2.trans second, ?_, ?_, ?_⟩
  · rw [DivisionBody.body_low fields state separate agrees, first, coordinate]
    exact step.1
  · rw [DivisionBody.body_high fields state separate agrees, first, coordinate]
    exact step.2
  · rw [DivisionBody.body_counter fields state separate, counter]
    apply BitVec.eq_of_toNat_eq
    have small : 32 - k < 4294967296 := by omega
    have nextSmall : 32 - (k + 1) < 4294967296 := by omega
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt nextSmall]
    norm_num
    omega

theorem invariant (fields : Fields) (dividend divisor : Word) (state : State) (k : Nat)
    (separate : Separate fields) (nonzero : 0 < divisor.toNat) (range : k ≤ 32)
    (ready : Ready fields dividend divisor state) :
    Invariant fields dividend divisor k (iterate fields k state) := by
  induction k with
  | zero => exact initial_invariant fields dividend divisor state ready
  | succ k ih => exact advance fields dividend divisor _ k separate nonzero (by omega) (ih (by omega))

theorem correct (fields : Fields) (dividend divisor : Word) (state : State)
    (separate : Separate fields) (nonzero : divisor ≠ 0)
    (ready : Ready fields dividend divisor state) :
    let final := iterate fields 32 state
    (final.memory (fields .low)).toNat = dividend.toNat / divisor.toNat ∧
    (final.memory (fields .high)).toNat = dividend.toNat % divisor.toNat ∧
    final.memory (fields .counter) = 0 := by
  have positive : 0 < divisor.toNat := by
    have nz : divisor.toNat ≠ 0 := fun eq => nonzero (BitVec.eq_of_toNat_eq eq)
    omega
  have facts := invariant fields dividend divisor state 32 separate positive (by decide) ready
  have arithmetic := full_word_division dividend divisor nonzero
  rcases facts with ⟨_, _, low, high, counter⟩
  simpa [packed, arithmetic.1, arithmetic.2, Nat.mod_one] using And.intro low (And.intro high counter)

theorem accumulator (fields : Fields) (state : State) (k : Nat) (separate : Separate fields) :
    (iterate fields k state).accumulator = state.accumulator := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate, DivisionBody.body_accumulator fields _ separate, ih]

theorem frame (fields : Fields) (state : State) (k : Nat) (field : Nat)
    (outside : ∀ slot ∈ DivisionBody.written, field ≠ fields slot) :
    (iterate fields k state).memory field = state.memory field := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate, DivisionBody.body_frame fields _ field outside, ih]

@[expose] def repeatedBody (fields : Fields) : Nat → List Instruction
  | 0 => []
  | n + 1 => repeatedBody fields n ++ body fields

theorem repeated_execution (fields : Fields) (state : State) (k : Nat) :
    run (repeatedBody fields k) state = iterate fields k state := by
  induction k with
  | zero => rfl
  | succ k ih => rw [repeatedBody, run_append, ih]; rfl

theorem repeated_length (fields : Fields) (k : Nat) :
    (repeatedBody fields k).length = 23 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [repeatedBody, body_length, ih]; omega

theorem repeated_pure (fields : Fields) (state : State) (k : Nat) (codeField : Nat → Prop)
    (owned : ∀ slot ∈ DivisionBody.written, codeField (fields slot)) :
    PureRun codeField (repeatedBody fields k) state := by
  apply pure_of_destinations
  induction k with
  | zero => simp [repeatedBody]
  | succ k ih =>
      simp only [repeatedBody, List.mem_append]
      intro instruction member
      rcases member with old | current
      · exact ih instruction old
      · have destinations : ∀ op ∈ body fields, codeField (destination op) := by
          simp_all [body, DivisionBody.written, destination, selected,
            MultiplyWords.destination, Machine32.destination]
        exact destinations instruction current

end SmcTuring.Appendix.DivisionIteration

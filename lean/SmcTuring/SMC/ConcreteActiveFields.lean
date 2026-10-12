module
public import SmcTuring.SMC.ConcreteFreshFields

public section
namespace SmcTuring.SMC.Concrete

/-- The same image has a uniform executable storage region, with five actual
instructions per visited cell: exchange, owning store, two stack-reset MOVs,
and an explicit CALL. Sequential headers always have next PC = PC + 1. -/
@[expose] def activeField (index : Nat) : Int := (index : Int) + 40

@[expose] def activeInitial : State :=
  { acc := 39, stack := 0, pc := owner 40 - 1, carry := false
    memory := fun field => if field = topField then returnField + 1 else field }

@[expose] def activeAdvance (field : Int) (s : State) : State :=
  let exchanged := execute 1 (.exchange field) (owner field) s
  let stored := execute 1 (.store (field - 1)) (owner field + 1) exchanged
  let reset := execute 1 (.exchangeStack topField) (owner field + 2) stored
  let restored := execute 1 (.storeStack topField) (owner field + 3) reset
  execute 1 (.call (owner (field + 1) - 1)) (owner field + 4) restored

@[expose] def activeBoundary : Nat → State
  | 0 => activeInitial
  | n + 1 => activeAdvance (activeField n) (activeBoundary n)

@[expose] def activeMiddle (n : Nat) : State :=
  execute 1 (.exchange (activeField n)) (owner (activeField n)) (activeBoundary n)

theorem active_headers (field : Int) (large : 40 ≤ field) :
    headers (owner field - 1) = some (.exchange (.fixed field), owner field) ∧
    headers (owner field + 1) = some (.exchangeStack topField, owner field + 2) ∧
    headers (owner field + 2) = some (.storeStack topField, owner field + 3) ∧
    headers (owner field + 3) = some (.call (.fixed (owner (field + 1) - 1)), owner field + 4) := by
  have nonnegative : 0 ≤ field := by omega
  have successor : 0 ≤ field + 1 := by omega
  simp only [owner, nonnegative, successor, ite_true]
  have natural : (field.toNat : Int) = field := Int.toNat_of_nonneg nonnegative
  have m0 : (-(-8 * (field + 1) - 1)).toNat = 8 * (field.toNat + 1) + 1 := by omega
  have m1 : (-(-8 * (field + 1) + 1)).toNat = 8 * field.toNat + 7 := by omega
  have m2 : (-(-8 * (field + 1) + 2)).toNat = 8 * field.toNat + 6 := by omega
  have m3 : (-(-8 * (field + 1) + 3)).toNat = 8 * field.toNat + 5 := by omega
  have low : 40 ≤ field.toNat := by omega
  have neg0 : ¬ 0 ≤ -8 * (field + 1) - 1 := by omega
  have neg1 : ¬ 0 ≤ -8 * (field + 1) + 1 := by omega
  have neg2 : ¬ 0 ≤ -8 * (field + 1) + 2 := by omega
  have neg3 : ¬ 0 ≤ -8 * (field + 1) + 3 := by omega
  have index0 : ¬ (8 * (field.toNat + 1) + 1 - 1) / 2 < 38 := by omega
  have index1 : ¬ (8 * field.toNat + 7 - 1) / 2 < 38 := by omega
  have index2 : ¬ (8 * field.toNat + 6 - 1) / 2 < 38 := by omega
  have index3 : ¬ (8 * field.toNat + 5 - 1) / 2 < 38 := by omega
  have large0 : 320 ≤ 8 * (field.toNat + 1) + 1 := by omega
  have large1 : 320 ≤ 8 * field.toNat + 7 := by omega
  have large2 : 320 ≤ 8 * field.toNat + 6 := by omega
  have large3 : 320 ≤ 8 * field.toNat + 5 := by omega
  simp (disch := omega) [headers, storageHeader, m0, m1, m2, m3]
  have noControl : ¬ 1 ≤ -8 * (field + 1) := by omega
  have cutoff0 : ¬ (25 ≤ 8 * (field.toNat + 1) / 2 ∧ 8 * (field.toNat + 1) / 2 < 38) := by omega
  have cutoff1 : ¬ (25 ≤ (8 * field.toNat + 6) / 2 ∧ (8 * field.toNat + 6) / 2 < 38) := by omega
  have cutoff2 : ¬ (25 ≤ (8 * field.toNat + 5) / 2 ∧ (8 * field.toNat + 5) / 2 < 38) := by omega
  have cutoff3 : ¬ (25 ≤ (8 * field.toNat + 4) / 2 ∧ (8 * field.toNat + 4) / 2 < 38) := by omega
  have quotient0 : (8 * (field.toNat + 1) + 1) / 8 - 1 = field.toNat := by omega
  have quotient3 : (8 * field + 5) / 8 = field := by omega
  have castQuotient0 : ((8 * (field.toNat + 1) + 1 : Nat) : Int) / 8 = field + 1 := by
    simp only [Int.natCast_add, Int.natCast_mul, natural]
    omega
  have castQuotient3 : ((8 * field.toNat + 5 : Nat) : Int) / 8 = field := by
    simp only [Int.natCast_add, Int.natCast_mul, natural]
    omega
  have region0 : 319 ≤ 8 * (field.toNat + 1) := by omega
  have region1 : 313 ≤ 8 * field.toNat := by omega
  have region2 : 314 ≤ 8 * field.toNat := by omega
  have region3 : 315 ≤ 8 * field.toNat := by omega
  simp [noControl, neg1, neg2, neg3, cutoff0, cutoff1, cutoff2, cutoff3, quotient0, quotient3,
    castQuotient0, castQuotient3, region0, region1, region2, region3, natural]
  all_goals omega

theorem active_invariant (n : Nat) :
    (activeBoundary n).acc = activeField n - 1 ∧
    (activeBoundary n).pc = owner (activeField n) - 1 ∧
    (activeBoundary n).memory topField = returnField + 1 ∧
    ∀ field, activeField n ≤ field → (activeBoundary n).memory field = field := by
  induction n with
  | zero =>
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp [activeBoundary, activeInitial]
    · intro field high
      have separate : field ≠ topField := by simp [activeField, topField, metaField] at high ⊢; omega
      simp [activeBoundary, activeInitial, separate]
  | succ n ih =>
    have high : 40 ≤ activeField n := by simp [activeField]; omega
    have current := ih.2.2.2 (activeField n) (by omega)
    have fieldTop : activeField n ≠ topField := by simp [activeField, topField, metaField]; omega
    have previousTop : activeField n - 1 ≠ topField := by simp [activeField, topField, metaField]; omega
    have returnTop : returnField ≠ topField := by decide
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [activeBoundary, activeAdvance, execute, current]
      simp [activeField]; omega
    · simp [activeBoundary, activeAdvance, execute, activeField, Int.add_assoc]
    · simp [activeBoundary, activeAdvance, execute, write, fieldTop, previousTop,
        Ne.symm fieldTop, Ne.symm previousTop, ih.2.2.1, returnTop, Ne.symm returnTop]
    · intro field future
      have same : (activeBoundary n).memory field = field := ih.2.2.2 field (by simp [activeField] at future ⊢; omega)
      have different : field ≠ activeField n := by simp [activeField] at future ⊢; omega
      have previous : field ≠ activeField n - 1 := by simp [activeField] at future ⊢; omega
      have metadata : field ≠ topField ∧ field ≠ returnField := by
        simp [activeField, topField, returnField, metaField] at future ⊢; omega
      simp [activeBoundary, activeAdvance, execute, write, different, previous, metadata,
        fieldTop, previousTop, Ne.symm fieldTop, Ne.symm previousTop, ih.2.2.1, same]

theorem active_fetch_exchange (n : Nat) :
    fetch image (activeBoundary n) = some (.exchange (activeField n), owner (activeField n)) := by
  have placed := (active_headers (activeField n) (by simp [activeField]; omega)).1
  simp [fetch, image, (active_invariant n).2.1, placed, decode, Address.eval]

theorem active_fetch_owner (n : Nat) :
    fetch image (activeMiddle n) = some (.store (activeField n - 1), owner (activeField n) + 1) := by
  have placed := data_owner (activeField n) (by simp [activeField]; omega)
  simp [fetch, image, activeMiddle, execute, placed, decode, Address.eval, write, (active_invariant n).1]

theorem active_block (n : Nat) :
    runImage 1 image 5 (activeBoundary n) = some (activeBoundary (n + 1)) ∧
      PureSteps 1 image 5 (activeBoundary n) := by
  have inv := active_invariant n
  have placed := active_headers (activeField n) (by simp [activeField]; omega)
  have current := inv.2.2.2 (activeField n) (by omega)
  have topSeparate : activeField n ≠ topField := by simp [activeField, topField, metaField]; omega
  have previousSeparate : activeField n - 1 ≠ topField := by simp [activeField, topField, metaField]; omega
  have fetched := active_fetch_exchange n
  have ownerFetched := active_fetch_owner n
  have high : 40 ≤ activeField n := by simp [activeField]; omega
  rcases placed with ⟨h0, h1, h2, h3⟩
  have owning := data_owner (activeField n) (by simp [activeField]; omega)
  simp [runImage, step, PureSteps, activeBoundary, activeAdvance, fetch, image, execute,
    decode, Address.eval, h0, h1, h2, h3, owning,
    write, inv.1, inv.2.1, inv.2.2.1, current, topSeparate, previousSeparate,
    Ne.symm topSeparate, Ne.symm previousSeparate, WritesCode, footprint, Code]
  all_goals simp [topField, returnField, metaField] at *
  all_goals omega

theorem active_run_blocks (n : Nat) :
    runImage 1 image (5 * n) activeInitial = some (activeBoundary n) ∧
      PureSteps 1 image (5 * n) activeInitial := by
  induction n with
  | zero => exact ⟨rfl, trivial⟩
  | succ n ih =>
    have block := active_block n
    rw [Nat.mul_succ, run_image_add, ih.1, Option.bind_some,
      pure_steps_composition 1 image (5 * n) 5 activeInitial (activeBoundary n) ih.1]
    exact ⟨block.1, ih.2, block.2⟩

theorem active_runs_forever : RunsForever activeInitial := by
  intro count
  have longer := (active_run_blocks count).1
  have order : count ≤ 5 * count := by omega
  rw [show 5 * count = count + (5 * count - count) by omega, run_image_add] at longer
  cases earlier : runImage 1 image count activeInitial with
  | none => simp [earlier] at longer
  | some finish => exact ⟨finish, rfl⟩

theorem active_pure : PureComputation activeInitial := by
  intro count finish completed
  have longer := (active_run_blocks count).2
  have order : count ≤ 5 * count := by omega
  rw [show 5 * count = count + (5 * count - count) by omega,
    pure_steps_composition 1 image count (5 * count - count) activeInitial finish completed] at longer
  exact longer.1

theorem active_run_middle (n : Nat) :
    runImage 1 image (5 * n + 1) activeInitial = some (activeMiddle n) := by
  rw [run_image_add, (active_run_blocks n).1, Option.bind_some]
  simp [runImage, step, active_fetch_exchange, activeMiddle]

theorem active_field_changes (n : Nat) : FieldChangeAt activeInitial (5 * n) (activeField n) := by
  refine ⟨activeBoundary n, .exchange (activeField n), owner (activeField n),
    (active_run_blocks n).1, active_fetch_exchange n, ?_⟩
  have old := (active_invariant n).2.2.2 (activeField n) (by omega)
  simp only [execute, write, ite_true, (active_invariant n).1, old]
  omega

theorem active_unbounded_fields : UnboundedChangedFields activeInitial := by
  intro bound
  refine ⟨activeField bound, 5 * bound, by simp [activeField]; omega,
    data_is_code _ (by simp [activeField]; omega), active_field_changes bound,
    activeMiddle bound, owner (activeField bound) + 1, active_run_middle bound, rfl, ?_⟩
  simpa [activeMiddle, execute, write, (active_invariant bound).1] using active_fetch_owner bound

theorem active_infinitely_changes : InfinitelyChanges activeInitial := by
  intro bound
  exact ⟨5 * bound, by omega, field_change_is_code_change _ _ _
    (data_is_code _ (by simp [activeField]; omega)) (active_field_changes bound)⟩

theorem pure_unbounded_smc_witness :
    RunsForever activeInitial ∧ PureComputation activeInitial ∧
      InfinitelyChanges activeInitial ∧ UnboundedChangedFields activeInitial :=
  ⟨active_runs_forever, active_pure, active_infinitely_changes, active_unbounded_fields⟩

end SmcTuring.SMC.Concrete

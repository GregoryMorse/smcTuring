module
public import SmcTuring.Appendix.BranchAlgebra

public section

namespace SmcTuring.Appendix.Branching

open Machine32 BranchAlgebra

attribute [local simp] BitVec.sub_add_cancel BitVec.xor_assoc
attribute [local simp] BranchAlgebra.complement_mask BranchAlgebra.and_mask

structure Fields where
  x : Nat
  y : Nat
  mask : Nat
  displacement : Nat
  delta : Nat

/-- The printed temporary exchanges require distinct operand/scratch fields.
Byte overlap/alignment and ownership are separate source-layout obligations. -/
structure Separate (fields : Fields) : Prop where
  xy : fields.x ≠ fields.y
  xm : fields.x ≠ fields.mask
  xc : fields.x ≠ fields.displacement
  xd : fields.x ≠ fields.delta
  ym : fields.y ≠ fields.mask
  yc : fields.y ≠ fields.displacement
  yd : fields.y ≠ fields.delta
  mc : fields.mask ≠ fields.displacement
  md : fields.mask ≠ fields.delta
  cd : fields.displacement ≠ fields.delta

/-- Listing 10 through operand restoration, including the actual zero-mask MOV. -/
@[expose] def comparison (fields : Fields) (signed gt : Bool) : List Instruction :=
  [.store fields.mask 0] ++
  (if signed then [.xorConstant fields.x signBit] else []) ++
  [.exchange fields.x] ++
  (if signed then [.xorConstant fields.y signBit] else []) ++
  [.subtractAcc fields.y] ++
  (if gt then [] else [.negate fields.y]) ++
  [.sbbZero fields.mask] ++
  (if gt then [] else [.negate fields.y]) ++
  [.addAcc fields.y] ++
  (if signed then [.xorConstant fields.y signBit] else []) ++
  [.exchange fields.x] ++
  (if signed then [.xorConstant fields.x signBit] else [])

/-- Complete printed predicate/patch prefix, ending before stack exchange/CALL.
The supplied delta is the value of the target relocation expression; the
ambiguous printed target parameter and byte layout are not silently assumed. -/
@[expose] def program (fields : Fields) (signed gt notFlag : Bool) (delta : Word) : List Instruction :=
  [.store fields.displacement 0] ++ comparison fields signed gt ++
  (if notFlag then [] else [.complement fields.mask]) ++
  [.store fields.delta delta, .andField fields.mask fields.delta,
    .xorField fields.displacement fields.mask]

@[expose] def effect (fields : Fields) (signed gt notFlag : Bool) (delta : Word) (state : State) : Word :=
  if selected signed gt notFlag (state.memory fields.x) (state.memory fields.y) then delta else 0

@[expose] def updated (fields : Fields) (delta chosen : Word) (memory : Nat → Word) : Nat → Word :=
  write (write (write memory fields.delta delta) fields.mask chosen) fields.displacement chosen

theorem comparison_accumulator (fields : Fields) (signed gt : Bool) (state : State)
    (separate : Separate fields) :
    (run (comparison fields signed gt) state).accumulator = state.accumulator := by
  cases signed <;> cases gt <;>
    simp [comparison, run, execute, put, write, separate.xy, separate.xm, separate.ym,
      Ne.symm separate.xy, Ne.symm separate.xm, Ne.symm separate.ym]

section
attribute [local simp] BranchAlgebra.raw BranchAlgebra.normalized BranchAlgebra.flip

theorem comparison_memory (fields : Fields) (signed gt : Bool) (state : State)
    (separate : Separate fields) :
    (run (comparison fields signed gt) state).memory =
      write state.memory fields.mask (BranchAlgebra.mask (raw signed gt (state.memory fields.x) (state.memory fields.y))) := by
  have xy := separate.xy
  have xm := separate.xm
  have ym := separate.ym
  have yx := Ne.symm xy
  have mx := Ne.symm xm
  have my := Ne.symm ym
  cases signed <;> cases gt <;> funext field
  all_goals
    by_cases x : field = fields.x
    · subst field
      simp_all [comparison, run, execute, put, write]
    · by_cases y : field = fields.y
      · subst field
        simp_all [comparison, run, execute, put, write]
      · by_cases maskField : field = fields.mask
        · subst field
          simp_all [comparison, run, execute, put, write]
          split <;> simp_all [BranchAlgebra.mask]
        · simp_all [comparison, run, execute, put, write]

end

theorem accumulator (fields : Fields) (signed gt notFlag : Bool) (delta : Word) (state : State)
    (separate : Separate fields) :
    (run (program fields signed gt notFlag delta) state).accumulator = state.accumulator := by
  simp only [program, run_append, run, execute, put]
  cases notFlag <;> simpa [run, execute, put] using
    comparison_accumulator fields signed gt (put state fields.displacement 0 state.carry) separate

theorem memory (fields : Fields) (signed gt notFlag : Bool) (delta : Word) (state : State)
    (separate : Separate fields) :
    (run (program fields signed gt notFlag delta) state).memory =
      updated fields delta (effect fields signed gt notFlag delta state) state.memory := by
  have compare := comparison_memory fields signed gt
    (put state fields.displacement 0 state.carry) separate
  simp only [put] at compare
  rcases separate with ⟨xy, xm, xc, xd, ym, yc, yd, mc, md, cd⟩
  have yx := Ne.symm xy
  have mx := Ne.symm xm
  have cx := Ne.symm xc
  have dx := Ne.symm xd
  have my := Ne.symm ym
  have cy := Ne.symm yc
  have dy := Ne.symm yd
  have cm := Ne.symm mc
  have dm := Ne.symm md
  have dc := Ne.symm cd
  cases notFlag <;>
    simp only [program, run_append, Bool.false_eq_true, ite_false, ite_true, run, execute, put]
  all_goals
    rw [compare]
    funext field
    simp_all [updated, effect, selected, write]

theorem carry (fields : Fields) (signed gt notFlag : Bool) (delta : Word) (state : State) :
    (run (program fields signed gt notFlag delta) state).carry = false := by
  simp only [program, run_append]
  cases notFlag <;> rfl

theorem displacement (fields : Fields) (signed gt notFlag : Bool) (delta : Word) (state : State)
    (separate : Separate fields) :
    (run (program fields signed gt notFlag delta) state).memory fields.displacement =
      effect fields signed gt notFlag delta state := by
  rw [memory fields signed gt notFlag delta state separate]
  simp [updated]

theorem program_length (fields : Fields) (signed gt notFlag : Bool) (delta : Word) :
    (program fields signed gt notFlag delta).length =
      10 + (if signed then 4 else 0) + (if gt then 0 else 2) + (if notFlag then 0 else 1) := by
  cases signed <;> cases gt <;> cases notFlag <;> simp [program, comparison]

theorem owned_destinations (fields : Fields) (signed gt notFlag : Bool) (delta : Word)
    (instruction : Instruction) (member : instruction ∈ program fields signed gt notFlag delta) :
    destination instruction ∈ [fields.x, fields.y, fields.mask, fields.displacement, fields.delta] := by
  have all : ∀ op ∈ program fields signed gt notFlag delta,
      destination op ∈ [fields.x, fields.y, fields.mask, fields.displacement, fields.delta] := by
    cases signed <;> cases gt <;> cases notFlag <;> simp [program, comparison, destination]
  exact all instruction member

theorem pure (codeField : Nat → Prop) (fields : Fields) (signed gt notFlag : Bool)
    (delta : Word) (state : State)
    (owned : ∀ field ∈ [fields.x, fields.y, fields.mask, fields.displacement, fields.delta], codeField field) :
    PureRun codeField (program fields signed gt notFlag delta) state := by
  apply pure_of_destinations
  intro instruction member
  exact owned _ (owned_destinations fields signed gt notFlag delta instruction member)

/-- Distinct fields cannot be dropped: an aliased equality test samples the
original accumulator instead of a second original operand. -/
theorem alias_counterexample :
    let fields : Fields := ⟨1, 1, 2, 3, 4⟩
    let state : State := ⟨1, false, fun _ => 0⟩
    (run (program fields false false true 7) state).memory fields.displacement = 7 ∧
      state.memory fields.x = state.memory fields.y := by
  decide

@[expose] def swapFields (fields : Fields) : Fields := { fields with x := fields.y, y := fields.x }

@[expose] def relationProgram (fields : Fields) (signed : Bool) (relation : Relation) (delta : Word) : List Instruction :=
  match relation with
  | .lt => program (swapFields fields) signed true true delta
  | .le => program fields signed true false delta
  | .eq => program fields signed false false delta
  | .ne => program fields signed false true delta
  | .gt => program fields signed true true delta
  | .ge => program (swapFields fields) signed true false delta

theorem swap_separate (fields : Fields) (separate : Separate fields) : Separate (swapFields fields) :=
  ⟨Ne.symm separate.xy, separate.ym, separate.yc, separate.yd,
    separate.xm, separate.xc, separate.xd, separate.mc, separate.md, separate.cd⟩

theorem relation_memory (fields : Fields) (signed : Bool) (relation : Relation) (delta : Word)
    (state : State) (separate : Separate fields) :
    (run (relationProgram fields signed relation delta) state).memory =
      updated fields delta (if holds signed relation (state.memory fields.x) (state.memory fields.y) then delta else 0) state.memory := by
  calc
    _ = updated fields delta (if relationSelected signed relation (state.memory fields.x) (state.memory fields.y) then delta else 0) state.memory := by
      cases relation with
      | lt => exact memory (swapFields fields) signed true true delta state (swap_separate fields separate)
      | le => exact memory fields signed true false delta state separate
      | eq => exact memory fields signed false false delta state separate
      | ne => exact memory fields signed false true delta state separate
      | gt => exact memory fields signed true true delta state separate
      | ge => exact memory (swapFields fields) signed true false delta state (swap_separate fields separate)
    _ = _ := by
      have choose : (if relationSelected signed relation (state.memory fields.x) (state.memory fields.y) then delta else 0) =
          (if holds signed relation (state.memory fields.x) (state.memory fields.y) then delta else 0) := by
        simp only [all_relations, decide_eq_true_eq]
      exact congrArg (fun chosen => updated fields delta chosen state.memory) choose

theorem relation_displacement (fields : Fields) (signed : Bool) (relation : Relation) (delta : Word)
    (state : State) (separate : Separate fields) :
    (run (relationProgram fields signed relation delta) state).memory fields.displacement =
      if holds signed relation (state.memory fields.x) (state.memory fields.y) then delta else 0 := by
  rw [relation_memory fields signed relation delta state separate]
  simp [updated]

/-- The mathematical near-relative target follows from the actual patched
field. Fixed-width addition includes the x86 IP wrap convention; byte fetch,
validity and the code-backed stack/CALL tail remain separate obligations. -/
theorem relation_target (fields : Fields) (signed : Bool) (relation : Relation)
    (next target : Word) (state : State) (separate : Separate fields) :
    next + (run (relationProgram fields signed relation (target - next)) state).memory fields.displacement =
      if holds signed relation (state.memory fields.x) (state.memory fields.y) then target else next := by
  rw [relation_displacement fields signed relation (target - next) state separate]
  by_cases condition : holds signed relation (state.memory fields.x) (state.memory fields.y)
  · simp only [condition, ite_true]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  · simp [condition]

theorem relation_accumulator (fields : Fields) (signed : Bool) (relation : Relation) (delta : Word)
    (state : State) (separate : Separate fields) :
    (run (relationProgram fields signed relation delta) state).accumulator = state.accumulator := by
  cases relation with
  | lt => exact accumulator (swapFields fields) signed true true delta state (swap_separate fields separate)
  | le => exact accumulator fields signed true false delta state separate
  | eq => exact accumulator fields signed false false delta state separate
  | ne => exact accumulator fields signed false true delta state separate
  | gt => exact accumulator fields signed true true delta state separate
  | ge => exact accumulator (swapFields fields) signed true false delta state (swap_separate fields separate)

theorem relation_carry (fields : Fields) (signed : Bool) (relation : Relation) (delta : Word) (state : State) :
    (run (relationProgram fields signed relation delta) state).carry = false := by
  cases relation <;> simp [relationProgram, carry]

theorem relation_frame (fields : Fields) (signed : Bool) (relation : Relation) (delta : Word)
    (state : State) (separate : Separate fields) (field : Nat)
    (outside : field ∉ [fields.mask, fields.displacement, fields.delta]) :
    (run (relationProgram fields signed relation delta) state).memory field = state.memory field := by
  rw [relation_memory fields signed relation delta state separate]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  simp [updated, write, outside.1, outside.2.1, outside.2.2]

theorem relation_pure (codeField : Nat → Prop) (fields : Fields) (signed : Bool)
    (relation : Relation) (delta : Word) (state : State)
    (owned : ∀ field ∈ [fields.x, fields.y, fields.mask, fields.displacement, fields.delta], codeField field) :
    PureRun codeField (relationProgram fields signed relation delta) state := by
  have swapped : ∀ field ∈ [(swapFields fields).x, (swapFields fields).y,
      (swapFields fields).mask, (swapFields fields).displacement, (swapFields fields).delta], codeField field := by
    intro field member
    apply owned field
    simpa [swapFields, or_left_comm] using member
  cases relation with
  | lt => exact pure codeField (swapFields fields) signed true true delta state swapped
  | le => exact pure codeField fields signed true false delta state owned
  | eq => exact pure codeField fields signed false false delta state owned
  | ne => exact pure codeField fields signed false true delta state owned
  | gt => exact pure codeField fields signed true true delta state owned
  | ge => exact pure codeField (swapFields fields) signed true false delta state swapped

end SmcTuring.Appendix.Branching

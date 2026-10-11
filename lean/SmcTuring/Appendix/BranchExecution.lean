module
public import SmcTuring.Appendix.Branching
public import SmcTuring.Appendix.FieldRefinement

public section

namespace SmcTuring.Appendix.BranchExecution

abbrev State := ByteExecution.State
abbrev Word := BitVec 32

@[expose] def fields (layout : Branching.Fields) : List Nat :=
  [layout.x, layout.y, layout.mask, layout.displacement, layout.delta]

@[expose] def view (native : State) : Machine32.State :=
  { accumulator := native.accumulator, carry := native.carry, memory := FieldRefinement.readField native }

@[expose] def run (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) : State :=
  FieldRefinement.run (Branching.relationProgram layout signed relation delta) native

/-- Initial agreement follows from actual byte loads, not supplied word results. -/
theorem initial_agreement (layout : Branching.Fields) (native : State) :
    FieldRefinement.Agreement (fields layout) (view native) native := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem program_dependencies (layout : Branching.Fields) (signed gt notFlag : Bool) (delta : Word) :
    ∀ instruction ∈ Branching.program layout signed gt notFlag delta,
      ∀ field ∈ FieldRefinement.dependencies instruction, field ∈ fields layout := by
  cases signed <;> cases gt <;> cases notFlag <;>
    simp [Branching.program, Branching.comparison, FieldRefinement.dependencies,
      FieldRefinement.sources, Machine32.destination, fields]

theorem relation_dependencies (layout : Branching.Fields) (signed : Bool)
    (relation : BranchAlgebra.Relation) (delta : Word) :
    ∀ instruction ∈ Branching.relationProgram layout signed relation delta,
      ∀ field ∈ FieldRefinement.dependencies instruction, field ∈ fields layout := by
  cases relation with
  | lt | ge =>
    intro instruction member field dependency
    have belongs := program_dependencies (Branching.swapFields layout) signed true _ delta
      instruction member field dependency
    simpa [fields, Branching.swapFields, or_left_comm] using belongs
  | le | eq | ne | gt => exact program_dependencies layout signed _ _ delta

/-- Effects of every branch prefix instruction refine the earlier relation
proof, under finite capacity and full-byte field separation. Actual fetch from
an emitted image is still a separate obligation. -/
theorem refinement (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) (physical : FieldRefinement.Layout (fields layout)) :
    FieldRefinement.Agreement (fields layout)
      (Machine32.run (Branching.relationProgram layout signed relation delta) (view native))
      (run layout signed relation delta native) :=
  FieldRefinement.simulate_run physical _ _ _ (initial_agreement layout native)
    (relation_dependencies layout signed relation delta)

theorem word_result (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) (physical : FieldRefinement.Layout (fields layout))
    (separate : Branching.Separate layout) (field : Nat) (member : field ∈ fields layout) :
    FieldRefinement.readField (run layout signed relation delta native) field =
      Branching.updated layout delta
        (if BranchAlgebra.holds signed relation (FieldRefinement.readField native layout.x)
          (FieldRefinement.readField native layout.y) then delta else 0)
        (FieldRefinement.readField native) field := by
  have words := (refinement layout signed relation delta native physical).words field member
  rw [Branching.relation_memory _ _ _ _ _ separate] at words
  exact words

theorem displacement (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) (physical : FieldRefinement.Layout (fields layout))
    (separate : Branching.Separate layout) :
    FieldRefinement.readField (run layout signed relation delta native) layout.displacement =
      if BranchAlgebra.holds signed relation (FieldRefinement.readField native layout.x)
        (FieldRefinement.readField native layout.y) then delta else 0 := by
  rw [word_result layout signed relation delta native physical separate _ (by simp [fields])]
  simp [Branching.updated]

theorem accumulator (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) (physical : FieldRefinement.Layout (fields layout))
    (separate : Branching.Separate layout) :
    (run layout signed relation delta native).accumulator = native.accumulator := by
  rw [(refinement layout signed relation delta native physical).accumulator,
    Branching.relation_accumulator _ _ _ _ _ separate]
  rfl

theorem stack (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) :
    (run layout signed relation delta native).stack = native.stack := FieldRefinement.run_stack _ _

theorem carry (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) (physical : FieldRefinement.Layout (fields layout)) :
    (run layout signed relation delta native).carry = false := by
  rw [(refinement layout signed relation delta native physical).carry, Branching.relation_carry]

theorem operand_x (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) (physical : FieldRefinement.Layout (fields layout))
    (separate : Branching.Separate layout) :
    FieldRefinement.readField (run layout signed relation delta native) layout.x = FieldRefinement.readField native layout.x := by
  rw [(refinement layout signed relation delta native physical).words _ (by simp [fields]),
    Branching.relation_frame _ _ _ _ _ separate _ (by
      simp [separate.xm, separate.xc, separate.xd])]
  rfl

theorem operand_y (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) (physical : FieldRefinement.Layout (fields layout))
    (separate : Branching.Separate layout) :
    FieldRefinement.readField (run layout signed relation delta native) layout.y = FieldRefinement.readField native layout.y := by
  rw [(refinement layout signed relation delta native physical).words _ (by simp [fields]),
    Branching.relation_frame _ _ _ _ _ separate _ (by
      simp [separate.ym, separate.yc, separate.yd])]
  rfl

theorem byte_frame (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) (physical : FieldRefinement.Layout (fields layout))
    (position : Nat) (outside : ∀ field ∈ fields layout, ¬Native.ByteMemory.Inside field 4 position) :
    (run layout signed relation delta native).memory position = native.memory position := by
  apply FieldRefinement.run_frame physical
  · intro instruction member
    exact relation_dependencies layout signed relation delta instruction member _
      (FieldRefinement.destination_dependency instruction)
  · intro instruction member
    exact outside _ (relation_dependencies layout signed relation delta instruction member _
      (FieldRefinement.destination_dependency instruction))

/-- Every byte outside the three FINAL scratch fields is restored, including
all bytes of x/y which the prefix temporarily exchanges and sign-normalizes. -/
theorem restored_byte_frame (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native : State) (physical : FieldRefinement.Layout (fields layout))
    (separate : Branching.Separate layout) (position : Nat)
    (outside : ∀ field ∈ [layout.mask, layout.displacement, layout.delta],
      ¬Native.ByteMemory.Inside field 4 position) :
    (run layout signed relation delta native).memory position = native.memory position := by
  by_cases inX : Native.ByteMemory.Inside layout.x 4 position
  · exact FieldRefinement.equal_word_byte _ _ layout.x (physical.fits _ (by simp [fields]))
      (operand_x layout signed relation delta native physical separate) position inX
  by_cases inY : Native.ByteMemory.Inside layout.y 4 position
  · exact FieldRefinement.equal_word_byte _ _ layout.y (physical.fits _ (by simp [fields]))
      (operand_y layout signed relation delta native physical separate) position inY
  apply byte_frame layout signed relation delta native physical position
  intro field member
  simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal <;> subst field
  · exact inX
  · exact inY
  · exact outside _ (by simp)
  · exact outside _ (by simp)
  · exact outside _ (by simp)

theorem owned (owned : Word → Prop) (layout : Branching.Fields) (signed : Bool)
    (relation : BranchAlgebra.Relation) (delta : Word) (native : State)
    (ownership : ∀ field ∈ fields layout, owned (FieldRefinement.address field)) :
    ByteExecution.OwnedRun owned
      (FieldRefinement.forms (Branching.relationProgram layout signed relation delta) native) native := by
  apply FieldRefinement.owned_run
  intro instruction member
  exact ownership _ (relation_dependencies layout signed relation delta instruction member _
    (FieldRefinement.destination_dependency instruction))

/-- This target identity is modular arithmetic on the resulting CALL field;
it does not assert that a tail or either continuation has already been fetched. -/
theorem modular_target (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (next target : Word) (native : State) (physical : FieldRefinement.Layout (fields layout))
    (separate : Branching.Separate layout) :
    next + FieldRefinement.readField (run layout signed relation (target - next) native) layout.displacement =
      if BranchAlgebra.holds signed relation (FieldRefinement.readField native layout.x)
        (FieldRefinement.readField native layout.y) then target else next := by
  rw [displacement layout signed relation (target - next) native physical separate]
  split
  · rw [BitVec.add_comm, BitVec.sub_add_cancel]
  · simp

theorem trace_displacement (layout : Branching.Fields) (signed : Bool) (relation : BranchAlgebra.Relation)
    (delta : Word) (native finish : State) (physical : FieldRefinement.Layout (fields layout))
    (separate : Branching.Separate layout)
    (trace : ByteExecution.Trace native
      (FieldRefinement.forms (Branching.relationProgram layout signed relation delta) native) finish) :
    FieldRefinement.readField finish layout.displacement =
      if BranchAlgebra.holds signed relation (FieldRefinement.readField native layout.x)
        (FieldRefinement.readField native layout.y) then delta else 0 := by
  rw [ByteExecution.trace_run trace, FieldRefinement.forms_run]
  exact displacement layout signed relation delta native physical separate

end SmcTuring.Appendix.BranchExecution

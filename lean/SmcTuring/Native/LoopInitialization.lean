module
public import SmcTuring.Native.ReadinessAtoms

public section

namespace SmcTuring.Native.LoopInitialization

open ControlImage RoleInitialization LayoutPass

/-- Exactly the initialized operand roles read as static metadata during a
source pass. The active pointer and mutable guard temporaries are excluded. -/
@[expose] def StaticOperand : RoleSeparation.Operand -> Prop
  | .field .top | .field .boundary | .field .zero | .field .terminal | .field .loop
  | .field .offsetZero | .field .offsetOne => True
  | .field _ | .reader .pointer => False
  | .reader _ | .capture _ => True
@[expose] def frozen (mode : Mode) (request : Request) (word : Word mode) : Prop :=
  exists role, StaticOperand role ∧ word = RoleSeparation.word mode request role
@[expose] def loop (mode : Mode) (request : Request) : LoopImage.Layout :=
  ⟨backedgeStart mode request, fieldPosition mode (roleLayout mode request) .loop⟩
@[expose] def pointer (mode : Mode) (request : Request) : Nat := pointerPosition mode (roleLayout mode request)
@[expose] def entry (mode : Mode) (request : Request) : Word mode :=
  Arithmetic.encodeNat mode (if request.closed then kernelStart mode request else boundaryStart mode request)

theorem frozen_owned (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (word : Word mode) (observed : frozen mode request word) : ProgramImage.owned mode (Assembly.context mode request assembly) word := by
  rcases observed with ⟨role, _, rfl⟩
  exact RoleSeparation.operand_owned mode request assembly role

theorem frozen_not_slot (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (word : Word mode) (observed : frozen mode request word) :
    word ≠ Arithmetic.encodeNat mode (fieldPosition mode (roleLayout mode request) .slot) := by
  rcases observed with ⟨role, immutable, rfl⟩
  intro same
  change RoleSeparation.word mode request role = RoleSeparation.word mode request (.field .slot) at same
  have equal := RoleSeparation.word_injective mode request assembly same
  cases equal
  exact immutable

/-- The literal indirect backedge belongs to the same complete byte image. -/
theorem backedge_within (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) :
    Fragment.Within mode (ControlPacking.place mode (backedgeStart mode request)
      (CallsImage.packets mode (backedgeStart mode request) (fieldPosition mode (roleLayout mode request) .top)
        (.indirect (fieldPosition mode (roleLayout mode request) .loop))))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) := by
  let leading := controlPrefix mode request assembly.reference ++
    SpacedPacking.adjacent mode (KernelPackets.flatten (KernelPackets.programSegments mode assembly.blocks))
  let trailing := EmittedImage.reserve request.hostSpan (fieldPieces mode (roleLayout mode request))
  have start : backedgeStart mode request = request.origin + SpacedPacking.size mode leading :=
    (LayoutPass.body_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled).symm
  let packets := CallsImage.packets mode (backedgeStart mode request) (fieldPosition mode (roleLayout mode request) .top)
    (.indirect (fieldPosition mode (roleLayout mode request) .loop))
  intro instruction member
  change instruction ∈ ControlPacking.place mode (backedgeStart mode request) packets at member
  rw [start] at member
  have included := SpacedPacking.adjacent_member mode request.origin leading trailing packets instruction member
  simpa only [leading, trailing, packets, Assembly.control, BoundedInitialization.image, EmittedImage.whole, EmittedImage.body, backedge, List.append_assoc] using included

/-- The source representation, intact bytes, initial static frames and actual
selected heap operand are all initialized from the constructed image. -/
theorem initial_invariant (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (positive : 0 < request.cells)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool) :
    ProgramImage.Invariant mode (Assembly.context mode request assembly) (Assembly.initial mode request assembly source accumulator stack carry)
      (frozen mode request) (pointer mode request) source (Assembly.initial mode request assembly source accumulator stack carry) := by
  refine ⟨Assembly.initially_represented mode request assembly source accumulator stack carry,
    Assembly.initially_intact mode request assembly source accumulator stack carry, fun _ _ => rfl, (0, false), positive, ?_⟩
  exact (BoundedInitialization.readers_initialized mode request assembly.toInput
    (SourceData.initialValues mode (gridBase mode request) source) .pointer).initialized

/-- Static backedge setup is derived for both closed and observed passes. It
assumes no program Setup, future trace or selected result. -/
theorem loop_setup (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (compact : ReadinessAtoms.Compact mode request)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool) :
    LoopImage.Setup mode (Assembly.context mode request assembly) (loop mode request)
      (Assembly.initial mode request assembly source accumulator stack carry) (frozen mode request) (pointer mode request) (entry mode request) := by
  have within := backedge_within mode request assembly
  have bounds := ReadinessAtoms.calls_bounds mode request assembly _ _ _ within
  have capacity := BoundedInitialization.metadata_fits mode request assembly.toInput
  refine {
    ranges := ReadinessAtoms.calls_ranges mode request assembly compact _ _ within
      (ReadinessAtoms.destination_bounds mode request assembly (.operand (.field .loop)))
    fits := Nat.lt_of_le_of_lt bounds.2 capacity
    enough := EmittedImage.grid_enough mode request
    gap := ?_
    within := within
    topOwned := BoundedInitialization.field_owned mode request assembly.toInput .top
    slotOwned := BoundedInitialization.field_owned mode request assembly.toInput .slot
    topFrozen := ⟨.field .top, trivial, rfl⟩
    targetFrozen := ⟨.field .loop, trivial, rfl⟩
    topValue := BoundedInitialization.stack_top_value mode request assembly.toInput _
    targetValue := (BoundedInitialization.fields_initialized mode request assembly.toInput _ .loop).initialized
    pointerNotSlot := RoleSeparation.reader_field_different mode request assembly .pointer .slot
    frozenNotSlot := frozen_not_slot mode request assembly }
  change request.origin + SpacedPacking.size mode (EmittedImage.whole mode request assembly.reference assembly.blocks) <= gridBase mode request - moffsOperandOffset mode
  rw [EmittedImage.whole_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled]
  exact EmittedImage.grid_gap mode request

end SmcTuring.Native.LoopInitialization

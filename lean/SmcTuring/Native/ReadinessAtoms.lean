module
public import SmcTuring.Native.RoleSeparation

public section

namespace SmcTuring.Native.ReadinessAtoms

open ControlImage RoleInitialization LayoutPass

/-- Fixed-address instructions only need a compact control/register region;
computed heap accesses use full-width MOFFS operands instead. -/
@[expose] def Compact (mode : Mode) (request : Request) : Prop :=
  Native.Layout.heapBase mode (gridBase mode request) - request.origin < 2 ^ (31 : Nat)
@[expose] def state (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (values : Nat -> Word mode) (pc : Nat) (accumulator stack : Word mode) (carry : Bool) : Execution.State mode :=
  ⟨Arithmetic.encodeNat mode pc, accumulator, stack, carry, BoundedInitialization.memory mode request assembly.toInput values⟩
@[expose] def reader (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (caller : Nat) (role : Reader) : ReadInvocationImage.Layout mode :=
  ⟨caller, readerPosition mode (roleLayout mode request) role, fieldPosition mode (roleLayout mode request) .top,
    fieldPosition mode (roleLayout mode request) .slot, request.origin, gridBase mode request,
    readerValue mode (roleLayout mode request) role, Assembly.control mode request assembly⟩

inductive Destination where
  | operand (role : RoleSeparation.Operand)
  | register (reg : Dolan.Mov.Register)
  deriving DecidableEq
@[expose] def destination (mode : Mode) (request : Request) : Destination -> Nat
  | .operand role => RoleSeparation.position mode request role
  | .register reg => SourceData.registerAddress mode (gridBase mode request) reg
@[expose] def scalar (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (start : Nat) (target : Destination) : ScalarImage.Layout mode :=
  ⟨start, destination mode request target, request.origin, gridBase mode request, Assembly.control mode request assembly⟩
@[expose] def update (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (caller : Nat) (role : Reader) (target : Destination) : ReadScalarImage.Layout mode :=
  ⟨reader mode request assembly caller role, destination mode request target⟩

theorem compact_delta (mode : Mode) (request : Request) (compact : Compact mode request) (next target : Nat)
    (nextInside : request.origin <= next ∧ next <= Native.Layout.heapBase mode (gridBase mode request))
    (targetInside : request.origin <= target ∧ target <= Native.Layout.heapBase mode (gridBase mode request)) :
    Relocation.SignedDelta next target := by
  unfold Compact at compact
  unfold Relocation.SignedDelta Relocation.delta
  change Native.Layout.heapBase mode (gridBase mode request) - request.origin < 2147483648 at compact
  change -(2147483648 : Int) <= (target : Int) - next ∧ (target : Int) - next < 2147483648
  constructor <;> omega

theorem destination_bounds (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (target : Destination) :
    request.origin <= destination mode request target ∧ destination mode request target <= Native.Layout.heapBase mode (gridBase mode request) := by
  cases target with
  | operand role =>
    have bounds := RoleSeparation.position_bounds mode request assembly role
    have gridBeforeHeap : gridBase mode request <= Native.Layout.heapBase mode (gridBase mode request) := Nat.le_add_right _ _
    change request.origin <= RoleSeparation.position mode request role ∧ _
    exact ⟨bounds.1, Nat.le_trans (Nat.le_of_lt bounds.2) gridBeforeHeap⟩
  | register reg =>
    have codeBefore := (RoleSeparation.position_bounds mode request assembly (.field .top))
    have below := Native.Layout.register_before_heap mode (gridBase mode request) (Dolan.Four.slot reg)
    have above : gridBase mode request <= SourceData.registerAddress mode (gridBase mode request) reg := Nat.le_add_right _ _
    change request.origin <= SourceData.registerAddress mode (gridBase mode request) reg ∧ _
    constructor
    · exact Nat.le_trans (Nat.le_trans codeBefore.1 (Nat.le_of_lt codeBefore.2)) above
    · change Native.Layout.registerField mode (gridBase mode request) (Dolan.Four.slot reg) <= _
      exact Nat.le_trans (Nat.le_add_right _ _) below

theorem destination_owned (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (target : Destination) :
    BoundedInitialization.owned mode request assembly.toInput (Arithmetic.encodeNat mode (destination mode request target)) := by
  cases target with
  | operand role => exact RoleSeparation.operand_owned mode request assembly role
  | register reg => exact SourceData.register_owned mode _ _ _ _ reg assembly.capacity

theorem destination_not_field (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (target : Destination) (field : Field) (different : target ≠ .operand (.field field)) :
    Arithmetic.encodeNat mode (destination mode request target) ≠ Arithmetic.encodeNat mode (fieldPosition mode (roleLayout mode request) field) := by
  cases target with
  | operand role =>
    intro same
    apply different
    exact congrArg Destination.operand (RoleSeparation.word_injective mode request assembly same)
  | register reg =>
    exact SourceData.register_not_before mode (gridBase mode request) request.cells (fieldPosition mode (roleLayout mode request) field)
      reg assembly.capacity (RoleSeparation.position_fits mode request assembly (.field field)) (BoundedInitialization.field_before_grid mode request field)

/-- Placement in the actual whole derives both caller bounds, including the
last CALL byte. No caller-address capacity condition is separately assumed. -/
theorem calls_bounds (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (start top : Nat) (transfer : CallsImage.Transfer)
    (within : Fragment.Within mode (ControlPacking.place mode start (CallsImage.packets mode start top transfer))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly))) :
    request.origin <= start ∧ start + CallsImage.totalSize mode transfer <= metadataLimit mode request := by
  have firstMember : CallsImage.firstEntry mode start top ∈ ControlPacking.place mode start (CallsImage.packets mode start top transfer) := by
    rw [CallsImage.placed_roles]; exact List.Mem.head _
  have lastMember : CallsImage.callEntry mode start transfer ∈ ControlPacking.place mode start (CallsImage.packets mode start top transfer) := by
    rw [CallsImage.placed_roles]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have lower := SpacedPacking.placed_lower mode (Assembly.control mode request assembly) request.origin _ (within _ firstMember)
  have upper := SpacedPacking.placed_upper mode (Assembly.control mode request assembly) request.origin _ (within _ lastMember)
  have ending := EmittedImage.whole_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled
  change request.origin + SpacedPacking.size mode (Assembly.control mode request assembly) = metadataLimit mode request at ending
  rw [ending] at upper
  constructor
  · exact lower
  · cases mode <;> cases transfer <;>
      simpa only [CallsImage.callEntry, Entry.bytes, Packet.bytes, instruction_length, CallsImage.callTarget,
        Calls.Target.form, instructionLength, CallsImage.totalSize, CallsImage.resetSize, MemoryOp.prefix,
        MemoryOp.trailer, wordPrefix, List.length_cons, List.length_nil, reduceCtorEq, ite_true, Nat.add_assoc] using upper

theorem calls_ranges (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (compact : Compact mode request)
    (start : Nat) (transfer : CallsImage.Transfer)
    (within : Fragment.Within mode (ControlPacking.place mode start
      (CallsImage.packets mode start (fieldPosition mode (roleLayout mode request) .top) transfer))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)))
    (targetInside : match transfer with | .relative target | .indirect target => request.origin <= target ∧ target <= Native.Layout.heapBase mode (gridBase mode request)) :
    CallsImage.Ranges mode start (fieldPosition mode (roleLayout mode request) .top) transfer := by
  have bounds := calls_bounds mode request assembly _ _ _ within
  have metadataBefore := BoundedInitialization.metadata_before_grid mode request
  have heapAfter : gridBase mode request <= Native.Layout.heapBase mode (gridBase mode request) := Nat.le_add_right _ _
  have topBounds := destination_bounds mode request assembly (.operand (.field .top))
  have oneSmall : CallsImage.oneSize mode <= CallsImage.totalSize mode transfer := by cases mode <;> cases transfer <;> simp only [CallsImage.oneSize, CallsImage.resetSize, CallsImage.totalSize] <;> omega
  have resetSmall : CallsImage.resetSize mode <= CallsImage.totalSize mode transfer := by cases mode <;> cases transfer <;> simp only [CallsImage.resetSize, CallsImage.totalSize] <;> omega
  refine ⟨fun _ => compact_delta mode request compact _ _ ⟨by omega, by omega⟩ topBounds,
    fun _ => compact_delta mode request compact _ _ ⟨by omega, by omega⟩ topBounds, ?_⟩
  cases transfer with
  | relative target =>
    apply compact_delta mode request compact _ _ _ targetInside
    simpa only [CallsImage.totalSize, Nat.add_assoc] using
      (show request.origin <= start + CallsImage.totalSize mode (.relative target) ∧
        start + CallsImage.totalSize mode (.relative target) <= Native.Layout.heapBase mode (gridBase mode request) from ⟨by omega, by omega⟩)
  | indirect target =>
    intro _
    apply compact_delta mode request compact _ _ _ targetInside
    simpa only [CallsImage.totalSize, Nat.add_assoc] using
      (show request.origin <= start + CallsImage.totalSize mode (.indirect target) ∧
        start + CallsImage.totalSize mode (.indirect target) <= Native.Layout.heapBase mode (gridBase mode request) from ⟨by omega, by omega⟩)

/-- Construct a literal initial read invocation from placed caller bytes and
the actual initialized reader/metadata image. All ownership and fits are derived. -/
theorem reader_ready (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (compact : Compact mode request)
    (positive : 0 < request.cells) (values : Nat -> Word mode) (caller : Nat) (role : Reader)
    (within : Fragment.Within mode (ControlPacking.place mode caller (CallsImage.packets mode caller
      (fieldPosition mode (roleLayout mode request) .top) (.relative (readerPosition mode (roleLayout mode request) role))))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)))
    (accumulator stack : Word mode) (carry : Bool) :
    ReadInvocationImage.Ready mode (reader mode request assembly caller role) (state mode request assembly values caller accumulator stack carry) := by
  let callee := readerPosition mode (roleLayout mode request) role
  have facts := BoundedInitialization.readers_initialized mode request assembly.toInput values role
  have calleeWithin : Fragment.Within mode (ControlPacking.place mode callee (ReadCalleeImage.packets mode callee
      (fieldPosition mode (roleLayout mode request) .top) (fieldPosition mode (roleLayout mode request) .slot) (readerValue mode (roleLayout mode request) role)))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) := facts.within
  have calleeFirst : ReaderImage.firstEntry mode callee ∈ SpacedPacking.place mode request.origin (Assembly.control mode request assembly) := by
    apply calleeWithin
    apply ReadCalleeImage.reader_within
    rw [ReaderImage.placed_roles]; exact List.Mem.head _
  have calleeLower := SpacedPacking.placed_lower mode (Assembly.control mode request assembly) request.origin _ calleeFirst
  have operandUpper := (RoleSeparation.position_bounds mode request assembly (.reader role)).2
  have heapAfter : gridBase mode request <= Native.Layout.heapBase mode (gridBase mode request) := Nat.le_add_right _ _
  have calleeInside : request.origin <= callee ∧ callee <= Native.Layout.heapBase mode (gridBase mode request) := ⟨calleeLower, by
    change callee + ReaderImage.labelOffset mode < gridBase mode request at operandUpper
    omega⟩
  have returnWithin := Fragment.within_trans mode _ _ _
    (ReadCalleeImage.call_within mode callee _ _ (readerValue mode (roleLayout mode request) role)) calleeWithin
  have callerBounds := calls_bounds mode request assembly _ _ _ within
  have capacity := BoundedInitialization.metadata_fits mode request assembly.toInput
  refine {
    location := rfl
    callerRanges := calls_ranges mode request assembly compact caller (.relative callee) within calleeInside
    calleeRanges := calls_ranges mode request assembly compact (ReadCalleeImage.callStart mode callee) (.indirect (fieldPosition mode (roleLayout mode request) .slot))
      returnWithin (destination_bounds mode request assembly (.operand (.field .slot)))
    callerFits := by
      change caller + CallsImage.totalSize mode (.relative callee) < _
      exact Nat.lt_of_le_of_lt callerBounds.2 capacity
    calleeFits := BoundedInitialization.reader_fits mode request assembly.toInput role.index.val role.index.isLt
    slotFits := RoleSeparation.position_fits mode request assembly (.field .slot)
    enough := EmittedImage.grid_enough mode request
    gap := by
      change request.origin + SpacedPacking.size mode (EmittedImage.whole mode request assembly.reference assembly.blocks) <= gridBase mode request - moffsOperandOffset mode
      rw [EmittedImage.whole_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled]
      exact EmittedImage.grid_gap mode request
    callerWithin := within
    calleeWithin := calleeWithin
    intact := EmittedImage.initially_intact mode request assembly.reference assembly.blocks assembly.endPC values assembly.compiled
    topValue := BoundedInitialization.stack_top_value mode request assembly.toInput values
    topOwned := BoundedInitialization.field_owned mode request assembly.toInput .top
    slotOwned := BoundedInitialization.field_owned mode request assembly.toInput .slot
    pointerOwned := ?_
    topDifferent := RoleSeparation.field_different mode request assembly .top .slot (by decide)
    labelDifferent := RoleSeparation.reader_field_different mode request assembly role .slot }
  change BoundedInitialization.owned mode request assembly.toInput
    (Execution.load mode (BoundedInitialization.memory mode request assembly.toInput values) (ReaderImage.label mode callee))
  have initialized := facts.initialized
  change Execution.load mode (BoundedInitialization.memory mode request assembly.toInput values) (ReaderImage.label mode callee) = readerValue mode (roleLayout mode request) role at initialized
  rw [initialized]
  exact BoundedInitialization.reader_target_owned mode request assembly.toInput positive role


theorem destination_fits (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (target : Destination) :
    destination mode request target < 2 ^ (8 * mode.wordBytes) := by
  cases target with
  | operand role => exact RoleSeparation.position_fits mode request assembly role
  | register reg => exact SourceData.register_fits mode _ _ reg assembly.capacity

/-- A placed scalar instruction obtains its initial readiness from capacity,
compact relocation geometry and its typed code-owned destination. -/
theorem scalar_ready (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (compact : Compact mode request)
    (values : Nat -> Word mode) (start : Nat) (target : Destination) (op : ScalarImage.Op)
    (member : ScalarImage.entry mode op (scalar mode request assembly start target) ∈
      SpacedPacking.place mode request.origin (Assembly.control mode request assembly))
    (accumulator stack : Word mode) (carry : Bool) :
    ScalarImage.Ready mode op (scalar mode request assembly start target) (state mode request assembly values start accumulator stack carry) := by
  have lower := SpacedPacking.placed_lower mode (Assembly.control mode request assembly) request.origin _ member
  change request.origin <= start at lower
  have upper := SpacedPacking.placed_upper mode (Assembly.control mode request assembly) request.origin _ member
  change start + (ScalarImage.entry mode op (scalar mode request assembly start target)).bytes.length <= _ at upper
  simp only [ScalarImage.entry, Entry.bytes, Packet.bytes, instruction_length, ScalarImage.form_size] at upper
  have ending := EmittedImage.whole_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled
  change request.origin + SpacedPacking.size mode (Assembly.control mode request assembly) = metadataLimit mode request at ending
  rw [ending] at upper
  have capacity := BoundedInitialization.metadata_fits mode request assembly.toInput
  have metadataBefore := BoundedInitialization.metadata_before_grid mode request
  have heapAfter : gridBase mode request <= Native.Layout.heapBase mode (gridBase mode request) := Nat.le_add_right _ _
  refine {
    location := rfl
    range := by
      intro _
      change Relocation.SignedDelta (start + ScalarImage.size mode op) (destination mode request target)
      exact compact_delta mode request compact _ _ ⟨by omega, by omega⟩ (destination_bounds mode request assembly target)
    codeFits := Nat.lt_of_le_of_lt upper capacity
    targetFits := destination_fits mode request assembly target
    enough := EmittedImage.grid_enough mode request
    gap := ?_
    member := member
    intact := EmittedImage.initially_intact mode request assembly.reference assembly.blocks assembly.endPC values assembly.compiled
    owned := destination_owned mode request assembly target }
  change request.origin + SpacedPacking.size mode (Assembly.control mode request assembly) <= gridBase mode request - moffsOperandOffset mode
  rw [ending]
  exact EmittedImage.grid_gap mode request

/-- Derive the read/update precondition from its literal enclosing fragment,
using only the initial byte image and destination separation. -/
theorem read_scalar_ready (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (compact : Compact mode request)
    (positive : 0 < request.cells) (values : Nat -> Word mode) (caller : Nat) (role : Reader) (target : Destination) (op : ScalarImage.Op)
    (within : Fragment.Within mode (ControlPacking.place mode caller
      (KernelPackets.readScalar mode op (update mode request assembly caller role target)).packets)
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)))
    (notSlot : target ≠ .operand (.field .slot)) (notTop : target ≠ .operand (.field .top))
    (accumulator stack : Word mode) (carry : Bool) :
    ReadScalarImage.Ready mode op (update mode request assembly caller role target) (state mode request assembly values caller accumulator stack carry) := by
  have finer := KernelPackets.read_scalar_placement mode op (update mode request assembly caller role target)
  have scalarMember : ScalarImage.entry mode op (ReadScalarImage.scalarLayout mode (update mode request assembly caller role target)) ∈
      SpacedPacking.place mode request.origin (Assembly.control mode request assembly) := by
    apply within; apply finer.2; exact List.Mem.head _
  exact ⟨reader_ready mode request assembly compact positive values caller role (Fragment.within_trans mode _ _ _ finer.1 within) accumulator stack carry,
    scalar_ready mode request assembly compact values (ReadScalarImage.scalarStart mode (update mode request assembly caller role target)) target op scalarMember accumulator stack carry,
    destination_not_field mode request assembly target .slot notSlot,
    Ne.symm (destination_not_field mode request assembly target .top notTop)⟩

end SmcTuring.Native.ReadinessAtoms

module
public import SmcTuring.Native.CompiledLayout

public section

namespace SmcTuring.Native.InvocationReadiness

open ControlImage RoleInitialization LayoutPass

variable (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
variable (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
variable (values : Nat -> Word mode) (accumulator stack : Word mode) (carry : Bool)

include compact positive

/-- The initial shared reader uses its actual emitted context and initialized
role. The shape equation is static lowerer data, not a readiness hypothesis. -/
theorem reader_for (layout : ReadInvocationImage.Layout mode) (role : Reader)
    (same : layout = ⟨layout.caller, readerPosition mode (roleLayout mode request) role,
      fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot,
      request.origin, gridBase mode request, readerValue mode (roleLayout mode request) role, assembly.reference⟩)
    (within : Fragment.Within mode (ControlPacking.place mode layout.caller (CallsImage.packets mode layout.caller layout.top (.relative layout.callee)))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly))) :
    ReadInvocationImage.Ready mode layout (ReadinessAtoms.state mode request assembly values layout.caller accumulator stack carry) := by
  have imageEq : Assembly.control mode request assembly = assembly.reference := assembly.consistent.symm
  have layoutEq : ReadinessAtoms.reader mode request assembly layout.caller role = layout := by
    change ⟨layout.caller, readerPosition mode (roleLayout mode request) role,
      fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot,
      request.origin, gridBase mode request, readerValue mode (roleLayout mode request) role, Assembly.control mode request assembly⟩ = layout
    rw [imageEq]; exact same.symm
  rw [same] at within
  simpa only [layoutEq] using ReadinessAtoms.reader_ready mode request assembly compact positive values layout.caller role within accumulator stack carry

theorem update_for (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode) (role : Reader) (target : ReadinessAtoms.Destination)
    (same : layout = ⟨⟨layout.reader.caller, readerPosition mode (roleLayout mode request) role,
      fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot,
      request.origin, gridBase mode request, readerValue mode (roleLayout mode request) role, assembly.reference⟩,
      ReadinessAtoms.destination mode request target⟩)
    (within : Fragment.Within mode (ControlPacking.place mode layout.reader.caller (KernelPackets.readScalar mode op layout).packets)
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)))
    (notSlot : target ≠ .operand (.field .slot)) (notTop : target ≠ .operand (.field .top)) :
    ReadScalarImage.Ready mode op layout (ReadinessAtoms.state mode request assembly values layout.reader.caller accumulator stack carry) := by
  have imageEq : Assembly.control mode request assembly = assembly.reference := assembly.consistent.symm
  have layoutEq : ReadinessAtoms.update mode request assembly layout.reader.caller role target = layout := by
    change ⟨⟨layout.reader.caller, readerPosition mode (roleLayout mode request) role,
      fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot,
      request.origin, gridBase mode request, readerValue mode (roleLayout mode request) role, Assembly.control mode request assembly⟩,
      ReadinessAtoms.destination mode request target⟩ = layout
    rw [imageEq]; exact same.symm
  have actualWithin : Fragment.Within mode (ControlPacking.place mode layout.reader.caller
      (KernelPackets.readScalar mode op (ReadinessAtoms.update mode request assembly layout.reader.caller role target)).packets)
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) := by simpa only [layoutEq] using within
  simpa only [layoutEq] using ReadinessAtoms.read_scalar_ready mode request assembly compact positive values layout.reader.caller role target
    op actualWithin notSlot notTop accumulator stack carry

/-- An actual placed caller plus the constructed guard certificate initializes
the guard invocation, including the distinct capture and return operands. -/
theorem guard_for (sense : GuardImage.Sense) (caller : Nat)
    (within : Fragment.Within mode (ControlPacking.place mode caller (CallsImage.packets mode caller
      (fieldPosition mode (roleLayout mode request) .top) (.relative (GuardPlacement.guard mode request assembly sense).setup.start)))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly))) :
    GuardInvocationImage.Ready mode ⟨caller, GuardPlacement.guard mode request assembly sense⟩
      (ReadinessAtoms.state mode request assembly values caller accumulator stack carry) := by
  let layout := GuardPlacement.guard mode request assembly sense
  have bodyReady := GuardReadiness.guard_ready mode request assembly compact positive values accumulator stack carry sense
  have captureWithin := GuardPlacement.capture_within mode request assembly sense
  have firstMember : ReaderImage.firstEntry mode layout.setup.start ∈ SpacedPacking.place mode request.origin (Assembly.control mode request assembly) := by
    apply captureWithin; rw [ReaderImage.placed_roles]; exact List.Mem.head _
  have lower := SpacedPacking.placed_lower mode (Assembly.control mode request assembly) request.origin _ firstMember
  change request.origin <= layout.setup.start at lower
  have upper := (RoleSeparation.position_bounds mode request assembly (.capture sense)).2
  have labelPosition : RoleSeparation.position mode request (.capture sense) = layout.setup.start + ReaderImage.labelOffset mode := by cases sense <;> rfl
  rw [labelPosition] at upper
  have heapAfter : gridBase mode request <= Native.Layout.heapBase mode (gridBase mode request) := Nat.le_add_right _ _
  have inside : request.origin <= layout.setup.start ∧ layout.setup.start <= Native.Layout.heapBase mode (gridBase mode request) := ⟨lower, by omega⟩
  have bounds := ReadinessAtoms.calls_bounds mode request assembly _ _ _ within
  have capacity := BoundedInitialization.metadata_fits mode request assembly.toInput
  have imageEq : Assembly.control mode request assembly = assembly.reference := assembly.consistent.symm
  refine {
    location := rfl
    callerRanges := ReadinessAtoms.calls_ranges mode request assembly compact _ _ within inside
    callerFits := Nat.lt_of_le_of_lt bounds.2 capacity
    callerWithin := ?_
    bodySetup := bodyReady
    captureDifferent := ?_ }
  · change Fragment.Within mode _ (SpacedPacking.place mode request.origin assembly.reference)
    rw [←imageEq]; exact within
  · cases sense with
    | base => exact RoleSeparation.capture_field_different mode request assembly .base .slot
    | offset => exact RoleSeparation.capture_field_different mode request assembly .offset .slot

@[expose] def store (caller : Nat) : StoreInvocationImage.Layout mode :=
  ⟨caller, readerPosition mode (roleLayout mode request) .pointer, fieldPosition mode (roleLayout mode request) .top,
    fieldPosition mode (roleLayout mode request) .slot, request.origin, gridBase mode request,
    readerValue mode (roleLayout mode request) .pointer, assembly.reference⟩

/-- The initial shared store enters the same MOFFS owner as the pointer reader.
Its heap-zero target, ownership and separation follow from initialization. -/
theorem store_for (caller : Nat)
    (within : Fragment.Within mode (ControlPacking.place mode caller (CallsImage.packets mode caller
      (fieldPosition mode (roleLayout mode request) .top) (.relative (StoreInvocationImage.entryPC mode (store mode request assembly caller)))))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly))) :
    StoreInvocationImage.Ready mode (store mode request assembly caller)
      (ReadinessAtoms.state mode request assembly values caller accumulator stack carry) := by
  let body := readerPosition mode (roleLayout mode request) .pointer
  have facts := BoundedInitialization.readers_initialized mode request assembly.toInput values .pointer
  have calleeWithin : Fragment.Within mode (ControlPacking.place mode body (ReadCalleeImage.packets mode body
      (fieldPosition mode (roleLayout mode request) .top) (fieldPosition mode (roleLayout mode request) .slot) (readerValue mode (roleLayout mode request) .pointer)))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) := facts.within
  have firstMember : ReaderImage.firstEntry mode body ∈ SpacedPacking.place mode request.origin (Assembly.control mode request assembly) := by
    apply calleeWithin; apply ReadCalleeImage.reader_within
    rw [ReaderImage.placed_roles]; exact List.Mem.head _
  have lower := SpacedPacking.placed_lower mode (Assembly.control mode request assembly) request.origin _ firstMember
  change request.origin <= body at lower
  have upper := (RoleSeparation.position_bounds mode request assembly (.reader .pointer)).2
  change body + ReaderImage.labelOffset mode < gridBase mode request at upper
  have prefixBound : ReaderImage.prefixSize mode <= ReaderImage.labelOffset mode := by cases mode <;> decide
  have heapAfter : gridBase mode request <= Native.Layout.heapBase mode (gridBase mode request) := Nat.le_add_right _ _
  have inside : request.origin <= StoreInvocationImage.entryPC mode (store mode request assembly caller) ∧
      StoreInvocationImage.entryPC mode (store mode request assembly caller) <= Native.Layout.heapBase mode (gridBase mode request) := by
    change request.origin <= body + ReaderImage.prefixSize mode ∧ body + ReaderImage.prefixSize mode <= _
    constructor <;> omega
  have returnWithin := Fragment.within_trans mode _ _ _ (ReadCalleeImage.call_within mode body _ _ (readerValue mode (roleLayout mode request) .pointer)) calleeWithin
  have bounds := ReadinessAtoms.calls_bounds mode request assembly _ _ _ within
  have capacity := BoundedInitialization.metadata_fits mode request assembly.toInput
  have imageEq : Assembly.control mode request assembly = assembly.reference := assembly.consistent.symm
  have points := facts.initialized
  change Execution.load mode (BoundedInitialization.memory mode request assembly.toInput values) (ReaderImage.label mode body) = SourceData.heapWord mode (gridBase mode request) (0, false) at points
  refine {
    location := rfl
    callerRanges := ReadinessAtoms.calls_ranges mode request assembly compact _ _ within inside
    calleeRanges := ReadinessAtoms.calls_ranges mode request assembly compact _ _ returnWithin
      (ReadinessAtoms.destination_bounds mode request assembly (.operand (.field .slot)))
    callerFits := Nat.lt_of_le_of_lt bounds.2 capacity
    bodyFits := BoundedInitialization.reader_fits mode request assembly.toInput 22 (by decide)
    slotFits := RoleSeparation.position_fits mode request assembly (.field .slot)
    enough := EmittedImage.grid_enough mode request
    gap := ?_
    callerWithin := ?_
    calleeWithin := ?_
    intact := ?_
    topValue := BoundedInitialization.stack_top_value mode request assembly.toInput values
    topOwned := ?_
    slotOwned := ?_
    pointerOwned := ?_
    targetDifferentTop := ?_
    targetDifferentSlot := ?_
    topDifferentSlot := RoleSeparation.field_different mode request assembly .top .slot (by decide)
    labelDifferentSlot := RoleSeparation.reader_field_different mode request assembly .pointer .slot }
  · change request.origin + SpacedPacking.size mode assembly.reference <= gridBase mode request - moffsOperandOffset mode
    rw [←imageEq]
    change request.origin + SpacedPacking.size mode (EmittedImage.whole mode request assembly.reference assembly.blocks) <= _
    rw [EmittedImage.whole_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled]
    exact EmittedImage.grid_gap mode request
  · change Fragment.Within mode _ (SpacedPacking.place mode request.origin assembly.reference)
    rw [←imageEq]; exact within
  · change Fragment.Within mode _ (SpacedPacking.place mode request.origin assembly.reference)
    rw [←imageEq]; exact calleeWithin
  · change SpacedCombinedImage.Intact mode assembly.reference request.origin (gridBase mode request) (BoundedInitialization.memory mode request assembly.toInput values)
    rw [←imageEq]
    exact EmittedImage.initially_intact mode request assembly.reference assembly.blocks assembly.endPC values assembly.compiled
  · change SpacedCombinedImage.Owned mode assembly.reference request.origin (gridBase mode request) _
    rw [←imageEq]; exact BoundedInitialization.field_owned mode request assembly.toInput .top
  · change SpacedCombinedImage.Owned mode assembly.reference request.origin (gridBase mode request) _
    rw [←imageEq]; exact BoundedInitialization.field_owned mode request assembly.toInput .slot
  · change SpacedCombinedImage.Owned mode assembly.reference request.origin (gridBase mode request)
      (Execution.load mode (BoundedInitialization.memory mode request assembly.toInput values) (ReaderImage.label mode body))
    rw [points, ←imageEq]; exact SourceData.heap_owned mode _ _ _ _ (0, false) assembly.capacity positive
  · change Execution.load mode (BoundedInitialization.memory mode request assembly.toInput values) (ReaderImage.label mode body) ≠ _
    rw [points]
    exact SourceData.heap_not_before mode _ _ _ (0, false) assembly.capacity positive
      (RoleSeparation.position_fits mode request assembly (.field .top)) (BoundedInitialization.field_before_grid mode request .top)
  · change Execution.load mode (BoundedInitialization.memory mode request assembly.toInput values) (ReaderImage.label mode body) ≠ _
    rw [points]
    exact SourceData.heap_not_before mode _ _ _ (0, false) assembly.capacity positive
      (RoleSeparation.position_fits mode request assembly (.field .slot)) (BoundedInitialization.field_before_grid mode request .slot)

end SmcTuring.Native.InvocationReadiness

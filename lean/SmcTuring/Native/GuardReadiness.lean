module
public import SmcTuring.Native.ReadinessAtoms

public section

namespace SmcTuring.Native.GuardReadiness

open ControlImage RoleInitialization LayoutPass

variable (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
variable (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
variable (values : Nat -> Word mode) (accumulator stack : Word mode) (carry : Bool)

include compact

private theorem scalar_for (sense : GuardImage.Sense) (op : ScalarImage.Op) (layout : ScalarImage.Layout mode) (field : Field)
    (same : layout = ⟨layout.start, fieldPosition mode (roleLayout mode request) field, request.origin, gridBase mode request, assembly.reference⟩)
    (included : KernelPackets.scalar mode op layout ∈ GuardPackets.segments mode (GuardPlacement.guard mode request assembly sense)) :
    ScalarImage.Ready mode op layout (ReadinessAtoms.state mode request assembly values layout.start accumulator stack carry) := by
  have imageEq : Assembly.control mode request assembly = assembly.reference := assembly.consistent.symm
  have layoutEq : ReadinessAtoms.scalar mode request assembly layout.start (.operand (.field field)) = layout := by
    change ⟨layout.start, fieldPosition mode (roleLayout mode request) field, request.origin, gridBase mode request, Assembly.control mode request assembly⟩ = layout
    rw [imageEq]; exact same.symm
  have member : ScalarImage.entry mode op (ReadinessAtoms.scalar mode request assembly layout.start (.operand (.field field))) ∈
      SpacedPacking.place mode request.origin (Assembly.control mode request assembly) := by
    rw [layoutEq]
    apply GuardPlacement.segment_within mode request assembly sense _ included
    exact List.Mem.head _
  simpa only [layoutEq] using ReadinessAtoms.scalar_ready mode request assembly compact values layout.start (.operand (.field field)) op member accumulator stack carry

include positive

private theorem reader_for (sense : GuardImage.Sense) (layout : ReadInvocationImage.Layout mode) (role : Reader)
    (same : layout = ⟨layout.caller, readerPosition mode (roleLayout mode request) role,
      fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot,
      request.origin, gridBase mode request, readerValue mode (roleLayout mode request) role, assembly.reference⟩)
    (included : KernelPackets.readCall mode layout ∈ GuardPackets.segments mode (GuardPlacement.guard mode request assembly sense)) :
    ReadInvocationImage.Ready mode layout (ReadinessAtoms.state mode request assembly values layout.caller accumulator stack carry) := by
  have imageEq : Assembly.control mode request assembly = assembly.reference := assembly.consistent.symm
  have layoutEq : ReadinessAtoms.reader mode request assembly layout.caller role = layout := by
    change ⟨layout.caller, readerPosition mode (roleLayout mode request) role,
      fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot,
      request.origin, gridBase mode request, readerValue mode (roleLayout mode request) role, Assembly.control mode request assembly⟩ = layout
    rw [imageEq]; exact same.symm
  have within := GuardPlacement.segment_within mode request assembly sense _ included
  rw [same] at within
  exact (show ReadInvocationImage.Ready mode layout _ from by
    simpa only [layoutEq] using ReadinessAtoms.reader_ready mode request assembly compact positive values layout.caller role within accumulator stack carry)

omit compact positive in
private theorem reader_pointer (role : Reader) :
    Execution.load mode (BoundedInitialization.memory mode request assembly.toInput values)
      (ReaderImage.label mode (readerPosition mode (roleLayout mode request) role)) = readerValue mode (roleLayout mode request) role :=
  (BoundedInitialization.readers_initialized mode request assembly.toInput values role).initialized

/-- The actual initialized guard capture/setup prefix needs no supplied Ready,
trace or future state. Its placement, pointers and all alias exclusions are derived. -/
theorem setup_ready (sense : GuardImage.Sense) :
    GuardSetupImage.Ready mode (GuardPlacement.guard mode request assembly sense).setup
      (ReadinessAtoms.state mode request assembly values (GuardPlacement.guard mode request assembly sense).setup.start accumulator stack carry) := by
  let layout := (GuardPlacement.guard mode request assembly sense).setup
  have capture := GuardPlacement.capture_constructed mode request assembly sense values
  have imageEq : Assembly.control mode request assembly = assembly.reference := assembly.consistent.symm
  refine {
    location := rfl
    captureFits := capture.fits
    captureWithin := by simpa only [imageEq, GuardPlacement.guard, LayoutPass.guard] using GuardPlacement.capture_within mode request assembly sense
    capturePointer := capture.initialized
    resumeSetup := ?_
    candidateSetup := ?_
    scratchSetup := ?_
    boundarySetup := ?_
    candidatePointer := reader_pointer mode request assembly values .candidate
    boundaryPointer := reader_pointer mode request assembly values .boundary
    candidateNotSlot := RoleSeparation.field_different mode request assembly .candidate .slot (by decide)
    boundaryNotSlot := RoleSeparation.field_different mode request assembly .boundary .slot (by decide)
    resumeNotTop := RoleSeparation.field_different mode request assembly .top .resume (by decide)
    resumeNotCandidate := RoleSeparation.field_different mode request assembly .candidate .resume (by decide)
    resumeNotBoundary := RoleSeparation.field_different mode request assembly .boundary .resume (by decide)
    scratchNotTop := RoleSeparation.field_different mode request assembly .top .scratch (by decide)
    scratchNotBoundary := RoleSeparation.field_different mode request assembly .boundary .scratch (by decide)
    scratchNotResume := RoleSeparation.field_different mode request assembly .resume .scratch (by decide)
    resumeNotSlot := RoleSeparation.field_different mode request assembly .resume .slot (by decide)
    scratchNotSlot := RoleSeparation.field_different mode request assembly .scratch .slot (by decide)
    resumeNotCandidateLabel := RoleSeparation.reader_field_different mode request assembly .candidate .resume
    resumeNotBoundaryLabel := RoleSeparation.reader_field_different mode request assembly .boundary .resume
    scratchNotBoundaryLabel := RoleSeparation.reader_field_different mode request assembly .boundary .scratch }
  · apply scalar_for mode request assembly compact values accumulator stack carry sense .store (GuardSetupImage.resumeLayout mode layout) .resume rfl
    apply List.mem_append_left; apply List.mem_append_left
    apply List.Mem.tail _; exact List.Mem.head _
  · apply reader_for mode request assembly compact positive values accumulator stack carry sense (GuardSetupImage.candidateLayout mode layout) .candidate rfl
    apply List.mem_append_left; apply List.mem_append_left
    apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
  · apply scalar_for mode request assembly compact values accumulator stack carry sense .store (GuardSetupImage.scratchLayout mode layout) .scratch rfl
    apply List.mem_append_left; apply List.mem_append_left
    apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
  · apply reader_for mode request assembly compact positive values accumulator stack carry sense (GuardSetupImage.boundaryLayout mode layout) .boundary rfl
    apply List.mem_append_left; apply List.mem_append_left
    apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _

/-- The SUB/read-zero/MOV/SBB stage is initialized from the literal zero
metadata and emitted scalar/caller packets. -/
theorem borrow_ready (sense : GuardImage.Sense) :
    BorrowMaskImage.Ready mode (GuardImage.borrowLayout mode (GuardPlacement.guard mode request assembly sense))
      (ReadinessAtoms.state mode request assembly values (GuardSetupImage.endPosition mode (GuardPlacement.guard mode request assembly sense).setup) accumulator stack carry) := by
  let layout := GuardImage.borrowLayout mode (GuardPlacement.guard mode request assembly sense)
  have subReady : ScalarImage.Ready mode .subtract (BorrowMaskImage.subLayout mode layout)
      (ReadinessAtoms.state mode request assembly values layout.start accumulator stack carry) := by
    apply scalar_for mode request assembly compact values accumulator stack carry sense .subtract (BorrowMaskImage.subLayout mode layout) .scratch rfl
    apply List.mem_append_left; apply List.mem_append_right; exact List.Mem.head _
  have readReady : ReadInvocationImage.Ready mode layout.reader
      (ReadinessAtoms.state mode request assembly values layout.reader.caller accumulator stack carry) := by
    apply reader_for mode request assembly compact positive values accumulator stack carry sense layout.reader .zero rfl
    apply List.mem_append_left; apply List.mem_append_right; apply List.Mem.tail _; exact List.Mem.head _
  have storeReady : ScalarImage.Ready mode .store (BorrowMaskImage.storeLayout mode layout)
      (ReadinessAtoms.state mode request assembly values (BorrowMaskImage.storeStart mode layout) accumulator stack carry) := by
    apply scalar_for mode request assembly compact values accumulator stack carry sense .store (BorrowMaskImage.storeLayout mode layout) .mask rfl
    apply List.mem_append_left; apply List.mem_append_right; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
  have sbbReady : ScalarImage.Ready mode .subtractBorrowZero (BorrowMaskImage.sbbLayout mode layout)
      (ReadinessAtoms.state mode request assembly values (BorrowMaskImage.storeStart mode layout + ScalarImage.size mode .store) accumulator stack carry) := by
    apply scalar_for mode request assembly compact values accumulator stack carry sense .subtractBorrowZero (BorrowMaskImage.sbbLayout mode layout) .mask rfl
    apply List.mem_append_left; apply List.mem_append_right; apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
  exact {
    subReady := subReady
    readSetup := readReady
    nextReader := rfl
    pointer := reader_pointer mode request assembly values .zero
    zeroValue := (BoundedInitialization.fields_initialized mode request assembly.toInput values .zero).initialized
    zeroNotSlot := RoleSeparation.field_different mode request assembly .zero .slot (by decide)
    scratchNotTop := RoleSeparation.field_different mode request assembly .top .scratch (by decide)
    scratchNotLabel := RoleSeparation.reader_field_different mode request assembly .zero .scratch
    scratchNotZero := RoleSeparation.field_different mode request assembly .zero .scratch (by decide)
    maskNotTop := RoleSeparation.field_different mode request assembly .top .mask (by decide)
    maskFits := sbbReady.targetFits
    maskOwned := sbbReady.owned
    storeRange := storeReady.range
    sbbRange := sbbReady.range
    codeFits := sbbReady.codeFits
    storeMember := storeReady.member
    sbbMember := sbbReady.member }

private theorem update_for (sense : GuardImage.Sense) (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode) (role : Reader)
    (same : layout = ⟨⟨layout.reader.caller, readerPosition mode (roleLayout mode request) role,
      fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot,
      request.origin, gridBase mode request, readerValue mode (roleLayout mode request) role, assembly.reference⟩,
      fieldPosition mode (roleLayout mode request) .selected⟩)
    (included : KernelPackets.readScalar mode op layout ∈ GuardPackets.segments mode (GuardPlacement.guard mode request assembly sense)) :
    ReadScalarImage.Ready mode op layout (ReadinessAtoms.state mode request assembly values layout.reader.caller accumulator stack carry) := by
  have imageEq : Assembly.control mode request assembly = assembly.reference := assembly.consistent.symm
  have layoutEq : ReadinessAtoms.update mode request assembly layout.reader.caller role (.operand (.field .selected)) = layout := by
    change ⟨⟨layout.reader.caller, readerPosition mode (roleLayout mode request) role,
      fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot,
      request.origin, gridBase mode request, readerValue mode (roleLayout mode request) role, Assembly.control mode request assembly⟩,
      fieldPosition mode (roleLayout mode request) .selected⟩ = layout
    rw [imageEq]; exact same.symm
  have within := GuardPlacement.segment_within mode request assembly sense _ included
  change Fragment.Within mode (ControlPacking.place mode layout.reader.caller (KernelPackets.readScalar mode op layout).packets)
    (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) at within
  have actualWithin : Fragment.Within mode (ControlPacking.place mode layout.reader.caller
      (KernelPackets.readScalar mode op (ReadinessAtoms.update mode request assembly layout.reader.caller role (.operand (.field .selected)))).packets)
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) := by simpa only [layoutEq] using within
  simpa only [layoutEq] using ReadinessAtoms.read_scalar_ready mode request assembly compact positive values layout.reader.caller role
    (.operand (.field .selected)) op actualWithin (by intro same; cases same) (by intro same; cases same) accumulator stack carry

/-- Both guard orientations derive the full initial selector and its final
indirect CALL from emitted placement and initialized metadata. -/
theorem selection_ready (sense : GuardImage.Sense) :
    GuardSelectionImage.Ready mode (GuardImage.selectionLayout mode (GuardPlacement.guard mode request assembly sense))
      (ReadinessAtoms.state mode request assembly values (GuardImage.selectionStart mode (GuardPlacement.guard mode request assembly sense)) accumulator stack carry) := by
  cases sense with
  | base =>
    let layout := GuardImage.selectionLayout mode (GuardPlacement.guard mode request assembly .base)
    have ready0 : ReadScalarImage.Ready mode .store (GuardSelectionImage.firstLayout mode layout)
        (ReadinessAtoms.state mode request assembly values (GuardSelectionImage.firstLayout mode layout).reader.caller accumulator stack carry) := by
      apply update_for mode request assembly compact positive values accumulator stack carry .base .store (GuardSelectionImage.firstLayout mode layout) .resume rfl
      apply List.mem_append_right
      exact List.Mem.head _
    have ready1 : ReadScalarImage.Ready mode .bitXor (GuardSelectionImage.secondLayout mode layout)
        (ReadinessAtoms.state mode request assembly values (GuardSelectionImage.secondLayout mode layout).reader.caller accumulator stack carry) := by
      apply update_for mode request assembly compact positive values accumulator stack carry .base .bitXor (GuardSelectionImage.secondLayout mode layout) .terminal rfl
      apply List.mem_append_right
      apply List.Mem.tail _; exact List.Mem.head _
    have ready2 : ReadScalarImage.Ready mode .bitAnd (GuardSelectionImage.thirdLayout mode layout)
        (ReadinessAtoms.state mode request assembly values (GuardSelectionImage.thirdLayout mode layout).reader.caller accumulator stack carry) := by
      apply update_for mode request assembly compact positive values accumulator stack carry .base .bitAnd (GuardSelectionImage.thirdLayout mode layout) .mask rfl
      apply List.mem_append_right
      apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
    have ready3 : ReadScalarImage.Ready mode .bitXor (GuardSelectionImage.fourthLayout mode layout)
        (ReadinessAtoms.state mode request assembly values (GuardSelectionImage.fourthLayout mode layout).reader.caller accumulator stack carry) := by
      apply update_for mode request assembly compact positive values accumulator stack carry .base .bitXor (GuardSelectionImage.fourthLayout mode layout) .resume rfl
      apply List.mem_append_right
      apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
    have callWithin : Fragment.Within mode (ControlPacking.place mode (GuardSelectionImage.callStart mode layout)
        (CallsImage.packets mode (GuardSelectionImage.callStart mode layout) layout.top (.indirect layout.selected)))
        (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) := by
      apply GuardPlacement.segment_within mode request assembly .base
        ⟨GuardSelectionImage.callStart mode layout, CallsImage.packets mode (GuardSelectionImage.callStart mode layout) layout.top (.indirect layout.selected)⟩
      apply List.mem_append_right
      apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
    have bounds := ReadinessAtoms.calls_bounds mode request assembly _ _ _ callWithin
    have capacity := BoundedInitialization.metadata_fits mode request assembly.toInput
    have imageEq : Assembly.control mode request assembly = assembly.reference := assembly.consistent.symm
    exact {
      firstReady := ready0
      secondSetup := ready1
      thirdSetup := ready2
      fourthSetup := ready3
      continuationPointer := reader_pointer mode request assembly values .resume
      terminalPointer := reader_pointer mode request assembly values .terminal
      maskPointer := reader_pointer mode request assembly values .mask
      continuationNotSelected := RoleSeparation.field_different mode request assembly .resume .selected (by decide)
      terminalNotSelected := RoleSeparation.field_different mode request assembly .terminal .selected (by decide)
      maskNotSelected := RoleSeparation.field_different mode request assembly .mask .selected (by decide)
      continuationNotSlot := RoleSeparation.field_different mode request assembly .resume .slot (by decide)
      terminalNotSlot := RoleSeparation.field_different mode request assembly .terminal .slot (by decide)
      maskNotSlot := RoleSeparation.field_different mode request assembly .mask .slot (by decide)
      continuationLabelNotSelected := RoleSeparation.reader_field_different mode request assembly .resume .selected
      terminalLabelNotSelected := RoleSeparation.reader_field_different mode request assembly .terminal .selected
      maskLabelNotSelected := RoleSeparation.reader_field_different mode request assembly .mask .selected
      callRanges := ReadinessAtoms.calls_ranges mode request assembly compact _ _ callWithin
        (ReadinessAtoms.destination_bounds mode request assembly (.operand (.field .selected)))
      callFits := Nat.lt_of_le_of_lt bounds.2 capacity
      callWithin := by
        change Fragment.Within mode _ (SpacedPacking.place mode request.origin assembly.reference)
        rw [←imageEq]; exact callWithin }
  | offset =>
    let layout := GuardImage.selectionLayout mode (GuardPlacement.guard mode request assembly .offset)
    have ready0 : ReadScalarImage.Ready mode .store (GuardSelectionImage.firstLayout mode layout)
        (ReadinessAtoms.state mode request assembly values (GuardSelectionImage.firstLayout mode layout).reader.caller accumulator stack carry) := by
      apply update_for mode request assembly compact positive values accumulator stack carry .offset .store (GuardSelectionImage.firstLayout mode layout) .terminal rfl
      apply List.mem_append_right
      exact List.Mem.head _
    have ready1 : ReadScalarImage.Ready mode .bitXor (GuardSelectionImage.secondLayout mode layout)
        (ReadinessAtoms.state mode request assembly values (GuardSelectionImage.secondLayout mode layout).reader.caller accumulator stack carry) := by
      apply update_for mode request assembly compact positive values accumulator stack carry .offset .bitXor (GuardSelectionImage.secondLayout mode layout) .resume rfl
      apply List.mem_append_right
      apply List.Mem.tail _; exact List.Mem.head _
    have ready2 : ReadScalarImage.Ready mode .bitAnd (GuardSelectionImage.thirdLayout mode layout)
        (ReadinessAtoms.state mode request assembly values (GuardSelectionImage.thirdLayout mode layout).reader.caller accumulator stack carry) := by
      apply update_for mode request assembly compact positive values accumulator stack carry .offset .bitAnd (GuardSelectionImage.thirdLayout mode layout) .mask rfl
      apply List.mem_append_right
      apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
    have ready3 : ReadScalarImage.Ready mode .bitXor (GuardSelectionImage.fourthLayout mode layout)
        (ReadinessAtoms.state mode request assembly values (GuardSelectionImage.fourthLayout mode layout).reader.caller accumulator stack carry) := by
      apply update_for mode request assembly compact positive values accumulator stack carry .offset .bitXor (GuardSelectionImage.fourthLayout mode layout) .terminal rfl
      apply List.mem_append_right
      apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
    have callWithin : Fragment.Within mode (ControlPacking.place mode (GuardSelectionImage.callStart mode layout)
        (CallsImage.packets mode (GuardSelectionImage.callStart mode layout) layout.top (.indirect layout.selected)))
        (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) := by
      apply GuardPlacement.segment_within mode request assembly .offset
        ⟨GuardSelectionImage.callStart mode layout, CallsImage.packets mode (GuardSelectionImage.callStart mode layout) layout.top (.indirect layout.selected)⟩
      apply List.mem_append_right
      apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
    have bounds := ReadinessAtoms.calls_bounds mode request assembly _ _ _ callWithin
    have capacity := BoundedInitialization.metadata_fits mode request assembly.toInput
    have imageEq : Assembly.control mode request assembly = assembly.reference := assembly.consistent.symm
    exact {
      firstReady := ready0
      secondSetup := ready1
      thirdSetup := ready2
      fourthSetup := ready3
      continuationPointer := reader_pointer mode request assembly values .terminal
      terminalPointer := reader_pointer mode request assembly values .resume
      maskPointer := reader_pointer mode request assembly values .mask
      continuationNotSelected := RoleSeparation.field_different mode request assembly .terminal .selected (by decide)
      terminalNotSelected := RoleSeparation.field_different mode request assembly .resume .selected (by decide)
      maskNotSelected := RoleSeparation.field_different mode request assembly .mask .selected (by decide)
      continuationNotSlot := RoleSeparation.field_different mode request assembly .terminal .slot (by decide)
      terminalNotSlot := RoleSeparation.field_different mode request assembly .resume .slot (by decide)
      maskNotSlot := RoleSeparation.field_different mode request assembly .mask .slot (by decide)
      continuationLabelNotSelected := RoleSeparation.reader_field_different mode request assembly .terminal .selected
      terminalLabelNotSelected := RoleSeparation.reader_field_different mode request assembly .resume .selected
      maskLabelNotSelected := RoleSeparation.reader_field_different mode request assembly .mask .selected
      callRanges := ReadinessAtoms.calls_ranges mode request assembly compact _ _ callWithin
        (ReadinessAtoms.destination_bounds mode request assembly (.operand (.field .selected)))
      callFits := Nat.lt_of_le_of_lt bounds.2 capacity
      callWithin := by
        change Fragment.Within mode _ (SpacedPacking.place mode request.origin assembly.reference)
        rw [←imageEq]; exact callWithin }

/-- A full static guard certificate constructed from the actual initialized
whole. Future execution readiness is subsequently transported by GuardImage. -/
theorem guard_ready (sense : GuardImage.Sense) :
    GuardImage.Ready mode (GuardPlacement.guard mode request assembly sense)
      (ReadinessAtoms.state mode request assembly values (GuardPlacement.guard mode request assembly sense).setup.start accumulator stack carry) :=
  ⟨setup_ready mode request assembly compact positive values accumulator stack carry sense,
    borrow_ready mode request assembly compact positive values accumulator stack carry sense,
    selection_ready mode request assembly compact positive values accumulator stack carry sense,
    RoleSeparation.guard_roles_injective mode request assembly sense⟩

end SmcTuring.Native.GuardReadiness

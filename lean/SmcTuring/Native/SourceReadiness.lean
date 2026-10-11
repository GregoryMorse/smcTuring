module
public import SmcTuring.Native.InvocationReadiness
public import SmcTuring.Native.SourceSeparation

public section

namespace SmcTuring.Native.SourceReadiness

open ControlImage RoleInitialization LayoutPass CompiledLayout

variable (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
variable (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
variable (values : Nat -> Word mode) (accumulator stack : Word mode) (carry : Bool)

@[expose] def immediate (pc : Nat) (destination : Dolan.Mov.Register) (choice : Bool) : ImmediateImage.Layout mode :=
  ⟨⟨KernelImage.reader mode (roles mode request assembly.reference) pc
      ((roles mode request assembly.reference).constantCallee choice) (Arithmetic.encodeNat mode ((roles mode request assembly.reference).constant choice)),
      SourceData.registerAddress mode (gridBase mode request) destination⟩,
    destination, (roles mode request assembly.reference).constant choice, choice, request.cells⟩
@[expose] def load (pc : Nat) (destination base offset : Dolan.Mov.Register) : LoadImage.Layout mode :=
  ⟨address mode request assembly pc base offset, destination, SourceValues.encodeWord mode (gridBase mode request) (.address 0)⟩
@[expose] def store (pc : Nat) (base offset source : Dolan.Mov.Register) : StoreImage.Layout mode :=
  ⟨address mode request assembly pc base offset, source, readerPosition mode (roleLayout mode request) (.register source),
    SourceData.registerWord mode (gridBase mode request) source, SourceValues.encodeWord mode (gridBase mode request) (.address 0)⟩

include compact positive

private theorem update_in_block (block : BlockImage.Block mode) (member : block ∈ assembly.blocks)
    (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode) (role : Reader) (target : ReadinessAtoms.Destination)
    (same : layout = ⟨⟨layout.reader.caller, readerPosition mode (roleLayout mode request) role,
      fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot,
      request.origin, gridBase mode request, readerValue mode (roleLayout mode request) role, assembly.reference⟩,
      ReadinessAtoms.destination mode request target⟩)
    (included : KernelPackets.readScalar mode op layout ∈ KernelPackets.segments mode block)
    (notSlot : target ≠ .operand (.field .slot)) (notTop : target ≠ .operand (.field .top)) :
    ReadScalarImage.Ready mode op layout (ReadinessAtoms.state mode request assembly values layout.reader.caller accumulator stack carry) :=
  InvocationReadiness.update_for mode request assembly compact positive values accumulator stack carry op layout role target same
    (Assembly.source_segment_within mode request assembly block member _ included) notSlot notTop

private theorem guard_in_block (block : BlockImage.Block mode) (member : block ∈ assembly.blocks)
    (layout : GuardInvocationImage.Layout mode) (sense : GuardImage.Sense)
    (same : layout = ⟨layout.caller, GuardPlacement.guard mode request assembly sense⟩)
    (included : KernelPackets.guardCall mode layout ∈ KernelPackets.segments mode block) :
    GuardInvocationImage.Ready mode layout (ReadinessAtoms.state mode request assembly values layout.caller accumulator stack carry) := by
  rcases layout with ⟨caller, guard⟩
  have guardEq := congrArg GuardInvocationImage.Layout.guard same
  change guard = GuardPlacement.guard mode request assembly sense at guardEq
  cases guardEq
  exact InvocationReadiness.guard_for mode request assembly compact positive values accumulator stack carry sense caller
    (Assembly.source_segment_within mode request assembly block member _ included)

omit compact positive in
private theorem reader_pointer (role : Reader) :
    Execution.load mode (BoundedInitialization.memory mode request assembly.toInput values)
      (ReaderImage.label mode (readerPosition mode (roleLayout mode request) role)) = readerValue mode (roleLayout mode request) role :=
  (BoundedInitialization.readers_initialized mode request assembly.toInput values role).initialized

/-- Every actual immediate block is ready in the literal initialized image;
its constant value, pointer and destination separation are derived. -/
theorem immediate_ready (pc : Nat) (destination : Dolan.Mov.Register) (choice : Bool)
    (member : BlockImage.Block.immediate (immediate mode request assembly pc destination choice) ∈ assembly.blocks) :
    ImmediateImage.Ready mode (immediate mode request assembly pc destination choice)
      (ReadinessAtoms.state mode request assembly values pc accumulator stack carry) := by
  cases choice with
  | false =>
    let layout := immediate mode request assembly pc destination false
    refine {
      unit := ?_
      target := rfl
      capacity := assembly.capacity
      slotBefore := BoundedInitialization.field_before_grid mode request .slot
      points := reader_pointer mode request assembly values .offsetZero
      constantValue := (BoundedInitialization.fields_initialized mode request assembly.toInput values .offsetZero).initialized
      constantNotSlot := RoleSeparation.field_different mode request assembly .offsetZero .slot (by decide) }
    apply update_in_block mode request assembly compact positive values accumulator stack carry (.immediate layout) member .store layout.unit .offsetZero (.register destination) rfl
    · exact List.Mem.head _
    · intro same; cases same
    · intro same; cases same
  | true =>
    let layout := immediate mode request assembly pc destination true
    refine {
      unit := ?_
      target := rfl
      capacity := assembly.capacity
      slotBefore := BoundedInitialization.field_before_grid mode request .slot
      points := reader_pointer mode request assembly values .offsetOne
      constantValue := (BoundedInitialization.fields_initialized mode request assembly.toInput values .offsetOne).initialized
      constantNotSlot := RoleSeparation.field_different mode request assembly .offsetOne .slot (by decide) }
    apply update_in_block mode request assembly compact positive values accumulator stack carry (.immediate layout) member .store layout.unit .offsetOne (.register destination) rfl
    · exact List.Mem.head _
    · intro same; cases same
    · intro same; cases same

/-- All original-memory address-stage setup is built from the actual lowerer
layout and its emitted snippets. No later pointer or Ready is assumed. -/
theorem address_ready (block : BlockImage.Block mode) (member : block ∈ assembly.blocks)
    (pc : Nat) (base offset : Dolan.Mov.Register)
    (included : forall segment, segment ∈ KernelPackets.addressSegments mode (address mode request assembly pc base offset) ->
      segment ∈ KernelPackets.segments mode block) :
    AddressImage.Ready mode (address mode request assembly pc base offset)
      (ReadinessAtoms.state mode request assembly values pc accumulator stack carry) := by
  let layout := address mode request assembly pc base offset
  have offsetRead : ReadScalarImage.Ready mode .store (OffsetGuardImage.readLayout mode layout.offset)
      (ReadinessAtoms.state mode request assembly values pc accumulator stack carry) := by
    apply update_in_block mode request assembly compact positive values accumulator stack carry block member .store
      (OffsetGuardImage.readLayout mode layout.offset) (.register offset) (.operand (.field .candidate)) rfl
    · apply included; exact List.Mem.head _
    · intro same; cases same
    · intro same; cases same
  have offsetGuard : GuardInvocationImage.Ready mode (OffsetGuardImage.guardLayout mode layout.offset)
      (ReadinessAtoms.state mode request assembly values (OffsetGuardImage.guardLayout mode layout.offset).caller accumulator stack carry) := by
    apply guard_in_block mode request assembly compact positive values accumulator stack carry block member
      (OffsetGuardImage.guardLayout mode layout.offset) .offset rfl
    apply included; apply List.Mem.tail _; exact List.Mem.head _
  have baseRead : ReadScalarImage.Ready mode .store (PointerImage.baseLayout mode (AddressImage.pointerLayout mode layout))
      (ReadinessAtoms.state mode request assembly values (AddressImage.pointerStart mode layout) accumulator stack carry) := by
    apply update_in_block mode request assembly compact positive values accumulator stack carry block member .store
      (PointerImage.baseLayout mode (AddressImage.pointerLayout mode layout)) (.register base) (.operand (.reader .pointer)) rfl
    · apply included; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
    · intro same; cases same
    · intro same; cases same
  have offsetAdd : ReadScalarImage.Ready mode .add (PointerImage.offsetLayout mode (AddressImage.pointerLayout mode layout))
      (ReadinessAtoms.state mode request assembly values (PointerImage.offsetLayout mode (AddressImage.pointerLayout mode layout)).reader.caller accumulator stack carry) := by
    apply update_in_block mode request assembly compact positive values accumulator stack carry block member .add
      (PointerImage.offsetLayout mode (AddressImage.pointerLayout mode layout)) (.register offset) (.operand (.reader .pointer)) rfl
    · apply included; apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
    · intro same; cases same
    · intro same; cases same
  have wordRead : ReadScalarImage.Ready mode .store (PointerImage.wordLayout mode (AddressImage.pointerLayout mode layout))
      (ReadinessAtoms.state mode request assembly values (PointerImage.wordLayout mode (AddressImage.pointerLayout mode layout)).reader.caller accumulator stack carry) := by
    apply update_in_block mode request assembly compact positive values accumulator stack carry block member .store
      (PointerImage.wordLayout mode (AddressImage.pointerLayout mode layout)) .pointerWord (.operand (.field .candidate)) rfl
    · apply included; apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
    · intro same; cases same
    · intro same; cases same
  have baseGuard : GuardInvocationImage.Ready mode (AddressImage.guardLayout mode layout)
      (ReadinessAtoms.state mode request assembly values (AddressImage.guardLayout mode layout).caller accumulator stack carry) := by
    apply guard_in_block mode request assembly compact positive values accumulator stack carry block member
      (AddressImage.guardLayout mode layout) .base rfl
    apply included; apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; apply List.Mem.tail _; exact List.Mem.head _
  exact {
    offsetSetup := {
      readSetup := offsetRead
      guardSetup := offsetGuard
      capacity := assembly.capacity
      positive := positive
      fieldsBefore := SourceSeparation.offset_fields_before mode request assembly pc base offset
      metadataDifferent := fun observed => SourceSeparation.guard_offset_separate mode request assembly .offset _ pc base offset observed .candidate
      sourcePointer := reader_pointer mode request assembly values (.register offset)
      boundary := (BoundedInitialization.fields_initialized mode request assembly.toInput values .boundary).initialized
      sense := rfl }
    pointerSetup := {
      baseSetup := baseRead
      offsetSetup := offsetAdd
      wordSetup := wordRead
      capacity := assembly.capacity
      fieldsBefore := SourceSeparation.pointer_fields_before mode request assembly pc base offset
      metadataDifferent := SourceSeparation.pointer_mutable_separate mode request assembly pc base offset
      pointerDifferent := RoleSeparation.reader_field_different mode request assembly .pointer .candidate
      basePointer := reader_pointer mode request assembly values (.register base)
      offsetPointer := reader_pointer mode request assembly values (.register offset)
      wordPointer := reader_pointer mode request assembly values .pointerWord }
    guardSetup := baseGuard
    pointerMetadataSeparate := SourceSeparation.pointer_offset_separate mode request assembly pc base offset
    guardOffsetSeparate := SourceSeparation.guard_offset_separate mode request assembly .base _ pc base offset
    guardPointerSeparate := SourceSeparation.guard_pointer_separate mode request assembly .base _ pc base offset
    pointerSeparate := SourceSeparation.pointer_control_separate mode request assembly pc base offset }

theorem load_ready (pc : Nat) (destination base offset : Dolan.Mov.Register)
    (member : BlockImage.Block.load (load mode request assembly pc destination base offset) ∈ assembly.blocks) :
    LoadImage.Ready mode (load mode request assembly pc destination base offset)
      (ReadinessAtoms.state mode request assembly values pc accumulator stack carry) := by
  let layout := load mode request assembly pc destination base offset
  refine ⟨address_ready mode request assembly compact positive values accumulator stack carry (.load layout) member pc base offset
    (fun segment belongs => List.mem_append_left _ belongs), ?_⟩
  apply update_in_block mode request assembly compact positive values accumulator stack carry (.load layout) member .store
    (LoadImage.readLayout mode layout) .pointer (.register destination) rfl
  · apply List.mem_append_right; exact List.Mem.head _
  · intro same; cases same
  · intro same; cases same

theorem store_ready (pc : Nat) (base offset source : Dolan.Mov.Register)
    (member : BlockImage.Block.store (store mode request assembly pc base offset source) ∈ assembly.blocks) :
    StoreImage.Ready mode (store mode request assembly pc base offset source)
      (ReadinessAtoms.state mode request assembly values pc accumulator stack carry) := by
  let layout := store mode request assembly pc base offset source
  have readWithin := Assembly.source_segment_within mode request assembly (.store layout) member
    (KernelPackets.readCall mode (StoreImage.readLayout mode layout)) (List.mem_append_right _ (List.Mem.head _))
  have storeWithin := Assembly.source_segment_within mode request assembly (.store layout) member
    (KernelPackets.storeCall mode (StoreImage.storeLayout mode layout)) (List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _)))
  refine {
    addressSetup := address_ready mode request assembly compact positive values accumulator stack carry (.store layout) member pc base offset
      (fun segment belongs => List.mem_append_left _ belongs)
    readSetup := InvocationReadiness.reader_for mode request assembly compact positive values accumulator stack carry (StoreImage.readLayout mode layout) (.register source) rfl readWithin
    storeSetup := InvocationReadiness.store_for mode request assembly compact positive values accumulator stack carry (StoreImage.storeLayout mode layout).caller storeWithin
    sourcePointer := reader_pointer mode request assembly values (.register source)
    sourceLabelSeparate := SourceSeparation.register_label_address_separate mode request assembly pc base offset source
    topBefore := BoundedInitialization.field_before_grid mode request .top }

/-- The complete emitted fixed source schedule has initial Ready for every
block, derived from one initialized byte image rather than supplied as a certificate. -/
theorem block_ready (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) :
    BlockImage.Ready mode block (ReadinessAtoms.state mode request assembly values (BlockImage.start mode block) accumulator stack carry) := by
  rcases block_lowered mode request assembly block member with ⟨pc, instruction, lowered⟩
  cases instruction with
  | immediate destination value =>
    cases value with
    | address cell => simp only [KernelImage.lower, reduceCtorEq] at lowered
    | offset choice =>
      simp only [KernelImage.lower, Option.some.injEq] at lowered
      subst block
      exact immediate_ready mode request assembly compact positive values accumulator stack carry pc destination choice member
  | load destination base offset =>
    simp only [KernelImage.lower, Option.some.injEq] at lowered
    subst block
    exact load_ready mode request assembly compact positive values accumulator stack carry pc destination base offset member
  | store base offset source =>
    simp only [KernelImage.lower, Option.some.injEq] at lowered
    subst block
    exact store_ready mode request assembly compact positive values accumulator stack carry pc base offset source member

end SmcTuring.Native.SourceReadiness

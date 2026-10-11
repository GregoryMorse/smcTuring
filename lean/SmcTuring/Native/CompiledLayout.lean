module
public import SmcTuring.Native.LoopInitialization
public import SmcTuring.Native.GuardReadiness

public section

namespace SmcTuring.Native.CompiledLayout

open ControlImage RoleInitialization LayoutPass

/-- Every compiled block has a literal lowerer witness, including its actual
start address and source operands. No shape assumptions are supplied. -/
theorem compile_membership (mode : Mode) (roles : KernelImage.Roles mode) (start : Nat)
    (source : List Dolan.Mov.Instruction) (blocks : List (BlockImage.Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode roles start source = some (blocks, endPC))
    (block : BlockImage.Block mode) (member : block ∈ blocks) :
    exists pc instruction, KernelImage.lower mode roles pc instruction = some block := by
  induction source generalizing start blocks endPC with
  | nil =>
    simp only [KernelImage.compile, Option.some.injEq, Prod.mk.injEq] at compiled
    rcases compiled with ⟨rfl, _⟩
    cases member
  | cons source rest ih =>
    cases first : KernelImage.lower mode roles start source with
    | none => simp only [KernelImage.compile, first, Option.bind_none, reduceCtorEq] at compiled
    | some firstBlock =>
      cases tail : KernelImage.compile mode roles (BlockImage.continuation mode firstBlock).toNat rest with
      | none => simp only [KernelImage.compile, first, Option.bind_some, tail, Option.map_none, reduceCtorEq] at compiled
      | some result =>
        rcases result with ⟨tailBlocks, tailEnd⟩
        simp only [KernelImage.compile, first, Option.bind_some, tail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        rcases List.mem_cons.mp member with same | later
        · subst block; exact ⟨start, source, first⟩
        · exact ih _ _ _ tail later

theorem block_lowered (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) :
    exists pc instruction, KernelImage.lower mode (roles mode request assembly.reference) pc instruction = some block :=
  compile_membership mode _ _ _ _ _ assembly.compiled block member

@[expose] def address (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) : AddressImage.Layout mode :=
  KernelImage.address mode (roles mode request assembly.reference) start base offset
@[expose] def offsetField : OffsetGuardImage.Field -> RoleSeparation.Operand
  | .candidate => .field .candidate | .resume => .field .resume | .scratch => .field .scratch
  | .slot => .field .slot | .mask => .field .mask | .selected => .field .selected
@[expose] def pointerField : PointerImage.Field -> RoleSeparation.Operand
  | .pointer => .reader .pointer | .candidate => .field .candidate | .slot => .field .slot
@[expose] def addressField : AddressImage.Field -> RoleSeparation.Operand
  | .control field => offsetField field | .pointer => .reader .pointer
@[expose] def guardMetadata (sense : GuardImage.Sense) : GuardInvocationImage.Metadata -> RoleSeparation.Operand
  | .top => .field .top | .capture => .capture sense
  | .candidateReader => .reader .candidate | .boundaryReader => .reader .boundary | .zeroReader => .reader .zero
  | .zero => .field .zero
  | .continuationReader => .reader (match sense with | .base => .resume | .offset => .terminal)
  | .alternativeReader => .reader (match sense with | .base => .terminal | .offset => .resume)
  | .maskReader => .reader .mask | .boundary => .field .boundary | .terminal => .field .terminal
@[expose] def pointerMetadata (base offset : Dolan.Mov.Register) : PointerImage.Metadata -> RoleSeparation.Operand
  | .top => .field .top | .baseReader => .reader (.register base)
  | .offsetReader => .reader (.register offset) | .wordReader => .reader .pointerWord

theorem offset_field_position (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (field : OffsetGuardImage.Field) :
    OffsetGuardImage.fieldAddress (address mode request assembly start base offset).offset field = RoleSeparation.position mode request (offsetField field) := by
  cases field <;> rfl

theorem pointer_field_position (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (field : PointerImage.Field) :
    PointerImage.fieldAddress (AddressImage.pointerLayout mode (address mode request assembly start base offset)) field = RoleSeparation.position mode request (pointerField field) := by
  cases field <;> rfl

theorem address_field_position (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (field : AddressImage.Field) :
    AddressImage.fieldAddress (address mode request assembly start base offset) field = RoleSeparation.position mode request (addressField field) := by
  cases field with
  | control field => exact offset_field_position mode request assembly start base offset field
  | pointer => rfl

theorem guard_metadata_word (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (sense : GuardImage.Sense) (caller : Nat) (observed : GuardInvocationImage.Metadata) :
    GuardInvocationImage.metadataWord mode ⟨caller, GuardPlacement.guard mode request assembly sense⟩ observed =
      RoleSeparation.word mode request (guardMetadata sense observed) := by
  cases sense <;> cases observed <;> rfl

theorem pointer_metadata_word (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (observed : PointerImage.Metadata) :
    PointerImage.metadataWord mode (AddressImage.pointerLayout mode (address mode request assembly start base offset)) observed =
      RoleSeparation.word mode request (pointerMetadata base offset observed) := by
  cases observed <;> rfl

theorem guard_metadata_frozen (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (sense : GuardImage.Sense) (caller : Nat) (observed : GuardInvocationImage.Metadata) :
    LoopInitialization.frozen mode request (GuardInvocationImage.metadataWord mode ⟨caller, GuardPlacement.guard mode request assembly sense⟩ observed) := by
  refine ⟨guardMetadata sense observed, ?_, guard_metadata_word mode request assembly sense caller observed⟩
  cases sense <;> cases observed <;> trivial

theorem pointer_metadata_frozen (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (observed : PointerImage.Metadata) :
    LoopInitialization.frozen mode request (PointerImage.metadataWord mode (AddressImage.pointerLayout mode (address mode request assembly start base offset)) observed) := by
  refine ⟨pointerMetadata base offset observed, ?_, pointer_metadata_word mode request assembly start base offset observed⟩
  cases observed <;> trivial

theorem address_static_frozen (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (word : Word mode)
    (observed : BlockImage.AddressStatic mode (address mode request assembly start base offset) word) : LoopInitialization.frozen mode request word := by
  cases observed with
  | top => exact ⟨.field .top, trivial, rfl⟩
  | offsetReader => exact ⟨.reader (.register offset), trivial, rfl⟩
  | offsetGuard role => exact guard_metadata_frozen mode request assembly .offset _ role
  | pointer role => exact pointer_metadata_frozen mode request assembly start base offset role
  | baseGuard role => exact guard_metadata_frozen mode request assembly .base _ role

/-- A source pass's static observations are actual immutable emitted roles. -/
theorem static_frozen (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) (word : Word mode)
    (observed : BlockImage.Static mode block word) : LoopInitialization.frozen mode request word := by
  rcases block_lowered mode request assembly block member with ⟨pc, instruction, lowered⟩
  cases instruction with
  | immediate destination value =>
    cases value with
    | address cell => simp only [KernelImage.lower, reduceCtorEq] at lowered
    | offset choice =>
      simp only [KernelImage.lower, Option.some.injEq] at lowered
      subst block
      cases observed with
      | immediateTop => exact ⟨.field .top, trivial, rfl⟩
      | immediateReader =>
        cases choice
        · exact ⟨.reader .offsetZero, trivial, rfl⟩
        · exact ⟨.reader .offsetOne, trivial, rfl⟩
      | immediateConstant =>
        cases choice
        · exact ⟨.field .offsetZero, trivial, rfl⟩
        · exact ⟨.field .offsetOne, trivial, rfl⟩
  | load destination base offset =>
    simp only [KernelImage.lower, Option.some.injEq] at lowered
    subst block
    cases observed with
    | loadAddress =>
      rename_i evidence
      exact address_static_frozen mode request assembly pc base offset word evidence
  | store base offset source =>
    simp only [KernelImage.lower, Option.some.injEq] at lowered
    subst block
    cases observed with
    | storeAddress =>
      rename_i evidence
      exact address_static_frozen mode request assembly pc base offset word evidence
    | storeReader => exact ⟨.reader (.register source), trivial, rfl⟩

private theorem offset_mutable (field : OffsetGuardImage.Field) : Not (LoopInitialization.StaticOperand (offsetField field)) := by
  cases field <;> exact id
private theorem pointer_mutable : Not (LoopInitialization.StaticOperand (.reader .pointer)) := id

theorem frozen_not_address_field (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (word : Word mode) (observed : LoopInitialization.frozen mode request word)
    (field : AddressImage.Field) : word ≠ Arithmetic.encodeNat mode (AddressImage.fieldAddress (address mode request assembly start base offset) field) := by
  rcases observed with ⟨role, immutable, rfl⟩
  rw [address_field_position]
  intro same
  change RoleSeparation.word mode request role = RoleSeparation.word mode request (addressField field) at same
  have equal := RoleSeparation.word_injective mode request assembly same
  cases equal
  cases field with
  | control field => exact offset_mutable field immutable
  | pointer => exact pointer_mutable immutable

theorem frozen_before_grid (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (word : Word mode) (observed : LoopInitialization.frozen mode request word) : word.toNat < gridBase mode request := by
  rcases observed with ⟨role, _, rfl⟩
  rw [RoleSeparation.word, Arithmetic.encode_nat_toNat mode _ (RoleSeparation.position_fits mode request assembly role)]
  exact (RoleSeparation.position_bounds mode request assembly role).2

/-- Each compiled source block's complete may-write set is disjoint from the
constructed immutable metadata. Source-data writes may alias source registers. -/
theorem frozen_outside (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) (word : Word mode)
    (observed : LoopInitialization.frozen mode request word) : Not (BlockImage.MayWrite mode block word) := by
  have before := frozen_before_grid mode request assembly word observed
  have registerAbove (reg : Dolan.Mov.Register) : gridBase mode request <= (SourceData.registerWord mode (gridBase mode request) reg).toNat := by
    rw [SourceData.register_toNat mode _ _ reg assembly.capacity]
    exact Nat.le_add_right _ _
  have heapAbove (position : Nat × Bool) (inside : position.1 < request.cells) : gridBase mode request <= (SourceData.heapWord mode (gridBase mode request) position).toNat := by
    rw [SourceData.heap_toNat mode _ _ position assembly.capacity inside]
    exact Nat.le_add_right _ _
  rcases block_lowered mode request assembly block member with ⟨pc, instruction, lowered⟩
  cases instruction with
  | immediate destination value =>
    cases value with
    | address cell => simp only [KernelImage.lower, reduceCtorEq] at lowered
    | offset choice =>
      simp only [KernelImage.lower, Option.some.injEq] at lowered
      subst block
      intro writes
      rcases writes with slot | target
      · exact LoopInitialization.frozen_not_slot mode request assembly word observed slot
      · have above := registerAbove destination
        change word = SourceData.registerWord mode (gridBase mode request) destination at target
        rw [←target] at above
        omega
  | load destination base offset =>
    simp only [KernelImage.lower, Option.some.injEq] at lowered
    subst block
    rintro ⟨field, same⟩
    cases field with
    | address field => exact frozen_not_address_field mode request assembly pc base offset word observed field same
    | destination =>
      have above := registerAbove destination
      change word = SourceData.registerWord mode (gridBase mode request) destination at same
      rw [←same] at above
      omega
  | store base offset source =>
    simp only [KernelImage.lower, Option.some.injEq] at lowered
    subst block
    rintro (⟨field, same⟩ | ⟨position, inside, same⟩)
    · exact frozen_not_address_field mode request assembly pc base offset word observed field same
    · have above := heapAbove position inside
      change word = SourceData.heapWord mode (gridBase mode request) position at same
      rw [←same] at above
      omega

end SmcTuring.Native.CompiledLayout

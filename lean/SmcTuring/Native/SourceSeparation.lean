module
public import SmcTuring.Native.CompiledLayout

public section

namespace SmcTuring.Native.SourceSeparation

open ControlImage RoleInitialization LayoutPass CompiledLayout

/-- Every original guard metadata operand is physically distinct from every
mutable offset-guard destination in the actual emitted image. -/
theorem guard_offset_separate (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (sense : GuardImage.Sense) (caller start : Nat) (base offset : Dolan.Mov.Register)
    (observed : GuardInvocationImage.Metadata) (field : OffsetGuardImage.Field) :
    GuardInvocationImage.metadataWord mode ⟨caller, GuardPlacement.guard mode request assembly sense⟩ observed ≠
      Arithmetic.encodeNat mode (OffsetGuardImage.fieldAddress (address mode request assembly start base offset).offset field) := by
  rw [guard_metadata_word, offset_field_position]
  change RoleSeparation.word mode request (guardMetadata sense observed) ≠ RoleSeparation.word mode request (offsetField field)
  intro same
  have equal := RoleSeparation.word_injective mode request assembly same
  cases sense <;> cases observed <;> cases field <;> cases equal

theorem guard_pointer_separate (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (sense : GuardImage.Sense) (caller start : Nat) (base offset : Dolan.Mov.Register)
    (observed : GuardInvocationImage.Metadata) (field : PointerImage.Field) :
    GuardInvocationImage.metadataWord mode ⟨caller, GuardPlacement.guard mode request assembly sense⟩ observed ≠
      Arithmetic.encodeNat mode (PointerImage.fieldAddress (AddressImage.pointerLayout mode (address mode request assembly start base offset)) field) := by
  rw [guard_metadata_word, pointer_field_position]
  change RoleSeparation.word mode request (guardMetadata sense observed) ≠ RoleSeparation.word mode request (pointerField field)
  intro same
  have equal := RoleSeparation.word_injective mode request assembly same
  cases sense <;> cases observed <;> cases field <;> cases equal

theorem pointer_offset_separate (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (observed : PointerImage.Metadata) (field : OffsetGuardImage.Field) :
    PointerImage.metadataWord mode (AddressImage.pointerLayout mode (address mode request assembly start base offset)) observed ≠
      Arithmetic.encodeNat mode (OffsetGuardImage.fieldAddress (address mode request assembly start base offset).offset field) := by
  rw [pointer_metadata_word, offset_field_position]
  change RoleSeparation.word mode request (pointerMetadata base offset observed) ≠ RoleSeparation.word mode request (offsetField field)
  intro same
  have equal := RoleSeparation.word_injective mode request assembly same
  cases observed <;> cases field <;> cases equal

theorem pointer_mutable_separate (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (observed : PointerImage.Metadata) (field : PointerImage.Field) :
    PointerImage.metadataWord mode (AddressImage.pointerLayout mode (address mode request assembly start base offset)) observed ≠
      Arithmetic.encodeNat mode (PointerImage.fieldAddress (AddressImage.pointerLayout mode (address mode request assembly start base offset)) field) := by
  rw [pointer_metadata_word, pointer_field_position]
  change RoleSeparation.word mode request (pointerMetadata base offset observed) ≠ RoleSeparation.word mode request (pointerField field)
  intro same
  have equal := RoleSeparation.word_injective mode request assembly same
  cases observed <;> cases field <;> cases equal

theorem offset_fields_before (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (field : OffsetGuardImage.Field) :
    OffsetGuardImage.fieldAddress (address mode request assembly start base offset).offset field < gridBase mode request := by
  rw [offset_field_position]
  exact (RoleSeparation.position_bounds mode request assembly (offsetField field)).2

theorem pointer_fields_before (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (field : PointerImage.Field) :
    PointerImage.fieldAddress (AddressImage.pointerLayout mode (address mode request assembly start base offset)) field < gridBase mode request := by
  rw [pointer_field_position]
  exact (RoleSeparation.position_bounds mode request assembly (pointerField field)).2

theorem pointer_control_separate (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset : Dolan.Mov.Register) (field : OffsetGuardImage.Field) :
    Arithmetic.encodeNat mode (AddressImage.pointerPosition mode (address mode request assembly start base offset)) ≠
      Arithmetic.encodeNat mode (OffsetGuardImage.fieldAddress (address mode request assembly start base offset).offset field) := by
  rw [offset_field_position]
  change RoleSeparation.word mode request (.reader .pointer) ≠ RoleSeparation.word mode request (offsetField field)
  intro same
  have equal := RoleSeparation.word_injective mode request assembly same
  cases field <;> cases equal

theorem register_label_address_separate (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (base offset register : Dolan.Mov.Register) (field : AddressImage.Field) :
    ReaderImage.label mode (readerPosition mode (roleLayout mode request) (.register register)) ≠
      Arithmetic.encodeNat mode (AddressImage.fieldAddress (address mode request assembly start base offset) field) := by
  rw [address_field_position]
  change RoleSeparation.word mode request (.reader (.register register)) ≠ RoleSeparation.word mode request (addressField field)
  intro same
  have equal := RoleSeparation.word_injective mode request assembly same
  cases field with
  | pointer => cases equal
  | control field => cases field <;> cases equal

end SmcTuring.Native.SourceSeparation

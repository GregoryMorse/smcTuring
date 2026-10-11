module
public import SmcTuring.Native.GuardPlacement

public section

namespace SmcTuring.Native.RoleSeparation

open RoleInitialization LayoutPass

inductive Operand where
  | field (role : Field)
  | reader (role : Reader)
  | capture (sense : GuardImage.Sense)
  deriving DecidableEq

@[expose] def position (mode : Mode) (request : Request) : Operand -> Nat
  | .field role => fieldPosition mode (roleLayout mode request) role
  | .reader role => readerPosition mode (roleLayout mode request) role + ReaderImage.labelOffset mode
  | .capture .base => baseGuardStart mode request + ReaderImage.labelOffset mode
  | .capture .offset => offsetGuardStart mode request + ReaderImage.labelOffset mode
@[expose] def word (mode : Mode) (request : Request) (role : Operand) : Word mode := Arithmetic.encodeNat mode (position mode request role)

private theorem region_order (mode : Mode) (request : Request) :
    readerLimit mode request <= baseGuardLimit mode request ∧ baseGuardLimit mode request <= kernelStart mode request ∧
      kernelStart mode request <= metadataStart mode request := by
  simp only [baseGuardLimit, baseGuardStart, offsetGuardStart, kernelStart, metadataStart, boundaryStart, backedgeStart,
    AlignedPacking.readerStart]
  omega

private theorem reader_affine (mode : Mode) (request : Request) (role : Reader) :
    readerPosition mode (roleLayout mode request) role = AlignedPacking.readerStart mode request.origin + PoolGeometry.readerStride mode * role.index.val :=
  PoolGeometry.reader_start_affine mode _ _ request.origin role.index.val

private theorem reader_index_injective : Function.Injective Reader.index := by
  intro first second same
  have lookup := congrArg (fun index : Fin 23 => readers[index.val]'(by rw [reader_count]; exact index.isLt)) same
  simpa only [reader_at_index] using lookup

private theorem reader_position_injective (mode : Mode) (request : Request) :
    Function.Injective (fun role => position mode request (.reader role)) := by
  intro first second same
  simp only [position, reader_affine] at same
  have positive : 0 < PoolGeometry.readerStride mode := by cases mode <;> decide
  apply reader_index_injective
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left positive (Nat.add_left_cancel (Nat.add_right_cancel same))

private theorem reader_before (mode : Mode) (request : Request) (role : Reader) :
    position mode request (.reader role) < readerLimit mode request := by
  have bounded := PoolGeometry.reader_bound mode (fieldPosition mode (roleLayout mode request) .top)
    (fieldPosition mode (roleLayout mode request) .slot) request.origin 23 role.index.val role.index.isLt
  rw [AlignedPool.reader_cursor mode _ _ request.origin 23] at bounded
  change readerPosition mode (roleLayout mode request) role + ReadCalleeImage.totalSize mode <= readerLimit mode request at bounded
  cases mode <;> simp only [position, ReaderImage.labelOffset, ReadCalleeImage.totalSize] at * <;> omega

private theorem metadata_after (mode : Mode) (request : Request) (role : Field) :
    metadataStart mode request <= position mode request (.field role) := by
  simp only [position, MetadataGeometry.field_affine, roleLayout]
  omega

private theorem base_bounds (mode : Mode) (request : Request) :
    readerLimit mode request <= position mode request (.capture .base) ∧
      position mode request (.capture .base) < baseGuardLimit mode request := by
  cases mode <;> simp only [position, baseGuardStart, baseGuardLimit, AlignedPacking.readerStart,
    ReaderImage.labelOffset, ByteLengths.guardSpan] <;> omega

private theorem offset_bounds (mode : Mode) (request : Request) :
    baseGuardLimit mode request <= position mode request (.capture .offset) ∧
      position mode request (.capture .offset) < kernelStart mode request := by
  cases mode <;> simp only [position, offsetGuardStart, kernelStart, AlignedPacking.readerStart,
    ReaderImage.labelOffset, ByteLengths.guardSpan] <;> omega

/-- Distinct semantic roles occupy distinct physical operand positions. The
proof uses the emitted region order, aligned affine pools and both guard sizes. -/
theorem position_injective (mode : Mode) (request : Request) : Function.Injective (position mode request) := by
  intro first second same
  have regions := region_order mode request
  have base := base_bounds mode request
  have offset := offset_bounds mode request
  cases first with
  | field first =>
    have lower := metadata_after mode request first
    cases second with
    | field second => exact congrArg Operand.field (MetadataGeometry.field_position_injective mode (roleLayout mode request) same)
    | reader second => have upper := reader_before mode request second; omega
    | capture sense => cases sense <;> omega
  | reader first =>
    have upper := reader_before mode request first
    cases second with
    | field second => have lower := metadata_after mode request second; omega
    | reader second => exact congrArg Operand.reader (reader_position_injective mode request same)
    | capture sense => cases sense <;> omega
  | capture sense =>
    cases sense <;> cases second with
    | field second => have lower := metadata_after mode request second; omega
    | reader second => have upper := reader_before mode request second; omega
    | capture second => cases second <;> first | rfl | omega

theorem position_bounds (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (role : Operand) :
    request.origin <= position mode request role ∧ position mode request role < gridBase mode request := by
  have regions := region_order mode request
  have readerExtent := LayoutPass.reader_extent mode request
  have readerLimit := BoundedInitialization.reader_limit_le mode request assembly.toInput
  have metadataBefore := BoundedInitialization.metadata_before_grid mode request
  have metadataExtent := LayoutPass.field_extent mode request
  cases role with
  | field role =>
    have lower := metadata_after mode request role
    exact ⟨by omega, BoundedInitialization.field_before_grid mode request role⟩
  | reader role =>
    have upper := reader_before mode request role
    constructor
    · simp only [position, reader_affine, AlignedPacking.readerStart]; omega
    · omega
  | capture sense =>
    cases sense
    · have bounds := base_bounds mode request; constructor <;> omega
    · have bounds := offset_bounds mode request; constructor <;> omega

theorem operand_owned (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (role : Operand) :
    BoundedInitialization.owned mode request assembly.toInput (word mode request role) := by
  cases role with
  | field role => exact BoundedInitialization.field_owned mode request assembly.toInput role
  | reader role => exact BoundedInitialization.reader_owned mode request assembly.toInput role
  | capture sense =>
    cases sense with
    | base =>
      simpa only [word, position, GuardPlacement.guard, LayoutPass.guard, ReaderImage.label] using
        (GuardPlacement.capture_constructed mode request assembly .base (fun _ => 0)).owned
    | offset =>
      simpa only [word, position, GuardPlacement.guard, LayoutPass.guard, ReaderImage.label] using
        (GuardPlacement.capture_constructed mode request assembly .offset (fun _ => 0)).owned

theorem position_fits (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (role : Operand) :
    position mode request role < 2 ^ (8 * mode.wordBytes) := by
  have metadataFits := BoundedInitialization.metadata_fits mode request assembly.toInput
  have readerLimit := BoundedInitialization.reader_limit_le mode request assembly.toInput
  have kernelBefore : kernelStart mode request <= backedgeStart mode request := Nat.le_add_right _ _
  have backedgeFits := Assembly.backedge_fits mode request assembly
  have regions := region_order mode request
  cases role with
  | field role => exact BoundedInitialization.field_fits mode request assembly.toInput role.index.val role.index.isLt
  | reader role => exact Nat.lt_trans (reader_before mode request role) (Nat.lt_of_le_of_lt readerLimit metadataFits)
  | capture sense =>
    cases sense
    · have bounds := base_bounds mode request; omega
    · have bounds := offset_bounds mode request; omega

theorem word_injective (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) : Function.Injective (word mode request) := by
  intro first second same
  apply position_injective mode request
  have natural := congrArg (fun value : Word mode => value.toNat) same
  simpa only [word, Arithmetic.encode_nat_toNat mode _ (position_fits mode request assembly first),
    Arithmetic.encode_nat_toNat mode _ (position_fits mode request assembly second)] using natural

theorem field_different (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (first second : Field) (different : first ≠ second) : word mode request (.field first) ≠ word mode request (.field second) := by
  intro same
  exact different (Operand.field.inj (word_injective mode request assembly same))

theorem reader_field_different (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (reader : Reader) (field : Field) : word mode request (.reader reader) ≠ word mode request (.field field) := by
  intro same
  cases word_injective mode request assembly same

theorem capture_field_different (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (sense : GuardImage.Sense) (field : Field) : word mode request (.capture sense) ≠ word mode request (.field field) := by
  intro same
  cases word_injective mode request assembly same

theorem reader_different (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (first second : Reader) (different : first ≠ second) : word mode request (.reader first) ≠ word mode request (.reader second) := by
  intro same
  exact different (Operand.reader.inj (word_injective mode request assembly same))

@[expose] def guardRole (sense : GuardImage.Sense) : GuardImage.Role -> Operand
  | .top => .field .top | .slot => .field .slot | .resume => .field .resume | .scratch => .field .scratch
  | .zero => .field .zero | .mask => .field .mask | .selected => .field .selected | .terminal => .field .terminal
  | .zeroLabel => .reader .zero
  | .continuationLabel => .reader (match sense with | .base => .resume | .offset => .terminal)
  | .alternativeLabel => .reader (match sense with | .base => .terminal | .offset => .resume)
  | .maskLabel => .reader .mask

private theorem guard_role_injective (sense : GuardImage.Sense) : Function.Injective (guardRole sense) := by
  intro first second same
  cases sense <;> cases first <;> cases second <;> simp_all [guardRole]

theorem guard_role_word (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (sense : GuardImage.Sense) (role : GuardImage.Role) :
    GuardImage.roleWord mode (GuardPlacement.guard mode request assembly sense) role = word mode request (guardRole sense role) := by
  cases sense <;> cases role <;> rfl

/-- The full guard's twelve role addresses are injective in the actual
constructed bounded image, discharging its static separation premise. -/
theorem guard_roles_injective (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (sense : GuardImage.Sense) :
    Function.Injective (GuardImage.roleWord mode (GuardPlacement.guard mode request assembly sense)) := by
  intro first second same
  rw [guard_role_word, guard_role_word] at same
  exact guard_role_injective sense (word_injective mode request assembly same)

end SmcTuring.Native.RoleSeparation

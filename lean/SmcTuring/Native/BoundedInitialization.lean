module
public import SmcTuring.Native.PoolGeometry

public section

namespace SmcTuring.Native.BoundedInitialization

open ControlImage RoleInitialization LayoutPass EmittedImage

/-- Static compilation and physical capacity data. This record contains no
execution trace, Ready predicate, intermediate state or simulation conclusion. -/
structure Input (mode : Mode) (request : Request) where
  reference : List (SpacedPacking.Piece mode)
  blocks : List (BlockImage.Block mode)
  endPC : Word mode
  compiled : KernelImage.compile mode (roles mode request reference) (kernelStart mode request)
    Dolan.Mov.kernelProgram = some (blocks, endPC)
  capacity : SourceData.Capacity mode (gridBase mode request) request.cells

@[expose] def image (mode : Mode) (request : Request) (input : Input mode request) : List (SpacedPacking.Piece mode) :=
  whole mode request input.reference input.blocks
@[expose] def memory (mode : Mode) (request : Request) (input : Input mode request) (values : Nat -> Word mode) : ByteMemory.Memory :=
  SpacedCombinedImage.image mode (image mode request input) request.origin (gridBase mode request) values
@[expose] def owned (mode : Mode) (request : Request) (input : Input mode request) : Word mode -> Prop :=
  SpacedCombinedImage.Owned mode (image mode request input) request.origin (gridBase mode request)

theorem metadata_before_grid (mode : Mode) (request : Request) : metadataLimit mode request < gridBase mode request := by
  cases mode <;> simp only [gridBase, Mode.stride, Mode.wordBytes] <;> omega

theorem metadata_fits (mode : Mode) (request : Request) (input : Input mode request) :
    metadataLimit mode request < 2 ^ (8 * mode.wordBytes) :=
  Nat.lt_trans (metadata_before_grid mode request) (SourceData.base_fits mode _ _ input.capacity)

theorem reader_limit_le (mode : Mode) (request : Request) (input : Input mode request) :
    readerLimit mode request <= metadataLimit mode request := by
  have readers := LayoutPass.reader_extent mode request
  have total := EmittedImage.whole_extent mode request input.reference input.blocks input.endPC input.compiled
  simp only [whole, body, controlPrefix, SpacedPacking.size_append] at total
  omega

/-- All twenty-three complete readers fit from one complete-image capacity
bound; no list of operand-by-operand fit assumptions is supplied. -/
theorem reader_fits (mode : Mode) (request : Request) (input : Input mode request) (index : Nat) (inside : index < 23) :
    AlignedPool.Fits mode (readerKind mode (roleLayout mode request))
      (AlignedPool.cursorAt mode (readerKind mode (roleLayout mode request)) request.origin index) := by
  have bounded := PoolGeometry.reader_bound mode (fieldPosition mode (roleLayout mode request) .top)
    (fieldPosition mode (roleLayout mode request) .slot) request.origin 23 index inside
  rw [AlignedPool.reader_cursor mode _ _ request.origin 23] at bounded
  change _ <= readerLimit mode request at bounded
  exact Nat.lt_of_le_of_lt bounded (Nat.lt_of_le_of_lt (reader_limit_le mode request input) (metadata_fits mode request input))

theorem field_fits (mode : Mode) (request : Request) (input : Input mode request) (index : Nat) (inside : index < 13) :
    AlignedPool.Fits mode .scalar (AlignedPool.cursorAt mode .scalar (metadataStart mode request) index) := by
  have bounded := PoolGeometry.scalar_bound mode (metadataStart mode request) 13 index inside
  have ending := metadata_fits mode request input
  change _ <= metadataLimit mode request at bounded
  change AlignedPacking.scalarStart mode (AlignedPool.cursorAt mode .scalar (metadataStart mode request) index) + moffsOperandOffset mode < _
  omega

theorem field_bound (mode : Mode) (request : Request) (role : Field) :
    fieldPosition mode (roleLayout mode request) role + mode.wordBytes <= metadataLimit mode request :=
  PoolGeometry.scalar_bound mode (metadataStart mode request) 13 role.index.val role.index.isLt

theorem field_before_grid (mode : Mode) (request : Request) (role : Field) :
    fieldPosition mode (roleLayout mode request) role < gridBase mode request := by
  have field := field_bound mode request role
  have metadata := metadata_before_grid mode request
  omega

theorem readers_initialized (mode : Mode) (request : Request) (input : Input mode request) (values : Nat -> Word mode) (role : Reader) :
    AlignedPool.Facts mode (readerKind mode (roleLayout mode request)) (readerCursor mode (roleLayout mode request) role)
      request.origin (gridBase mode request) (readerValue mode (roleLayout mode request) role) (image mode request input) values :=
  ImageInitialization.reader_initialized mode request input.reference input.blocks values (reader_fits mode request input) role

theorem fields_initialized (mode : Mode) (request : Request) (input : Input mode request) (values : Nat -> Word mode) (role : Field) :
    AlignedPool.Facts mode .scalar (fieldCursor mode (roleLayout mode request) role)
      request.origin (gridBase mode request) (fieldValue mode (roleLayout mode request) role) (image mode request input) values :=
  ImageInitialization.field_initialized mode request input.reference input.blocks input.endPC values input.compiled
    (field_fits mode request input) role

theorem field_owned (mode : Mode) (request : Request) (input : Input mode request) (role : Field) :
    owned mode request input (Arithmetic.encodeNat mode (fieldPosition mode (roleLayout mode request) role)) :=
  (fields_initialized mode request input (fun _ => 0) role).owned

theorem reader_owned (mode : Mode) (request : Request) (input : Input mode request) (role : Reader) :
    owned mode request input (ReaderImage.label mode (readerPosition mode (roleLayout mode request) role)) :=
  (readers_initialized mode request input (fun _ => 0) role).owned

/-- Every reader's initialized target is an actual code operand: source data,
metadata, or the single shared active pointer word. -/
theorem reader_target_owned (mode : Mode) (request : Request) (input : Input mode request)
    (positive : 0 < request.cells) (role : Reader) : owned mode request input (readerValue mode (roleLayout mode request) role) := by
  cases role with
  | register reg => exact SourceData.register_owned mode _ _ _ _ reg input.capacity
  | candidate => exact field_owned mode request input .candidate
  | boundary => exact field_owned mode request input .boundary
  | zero => exact field_owned mode request input .zero
  | resume => exact field_owned mode request input .resume
  | terminal => exact field_owned mode request input .terminal
  | mask => exact field_owned mode request input .mask
  | offsetZero => exact field_owned mode request input .offsetZero
  | offsetOne => exact field_owned mode request input .offsetOne
  | pointerWord => exact reader_owned mode request input .pointer
  | pointer => exact SourceData.heap_owned mode _ _ _ _ (0, false) input.capacity positive

theorem stack_top_value (mode : Mode) (request : Request) (input : Input mode request) (values : Nat -> Word mode) :
    Execution.load mode (memory mode request input values) (Arithmetic.encodeNat mode (fieldPosition mode (roleLayout mode request) .top)) =
      Arithmetic.encodeNat mode (fieldPosition mode (roleLayout mode request) .slot) + Arithmetic.encodeNat mode mode.wordBytes := by
  have initial := (fields_initialized mode request input values .top).initialized
  change Execution.load mode (memory mode request input values) (Arithmetic.encodeNat mode (fieldPosition mode (roleLayout mode request) .top)) =
      Arithmetic.encodeNat mode (fieldPosition mode (roleLayout mode request) .slot + mode.wordBytes) at initial
  rw [initial]
  exact (BitVec.ofNat_add_ofNat _ _).symm

end SmcTuring.Native.BoundedInitialization

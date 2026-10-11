module
public import SmcTuring.Native.EmittedImage

public section

namespace SmcTuring.Native.ImageInitialization

open ControlImage RoleInitialization LayoutPass EmittedImage

/-- The metadata pool occupies its computed physical position after the pure
body and unfetched host gap in the complete constructed image. -/
theorem metadata_within (mode : Mode) (request : Request) (reference : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode (roles mode request reference) (kernelStart mode request)
      Dolan.Mov.kernelProgram = some (blocks, endPC)) :
    Fragment.Within mode (SpacedPacking.place mode (metadataStart mode request) (fieldPieces mode (roleLayout mode request)))
      (SpacedPacking.place mode request.origin (whole mode request reference blocks)) := by
  intro entry member
  rw [whole, SpacedPacking.place_append, reserve_place, EmittedImage.body_extent mode request reference blocks endPC compiled]
  exact List.mem_append_right _ member

theorem reader_initialized (mode : Mode) (request : Request) (reference : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) (values : Nat -> Word mode)
    (fits : forall index, index < 23 -> AlignedPool.Fits mode (readerKind mode (roleLayout mode request))
      (AlignedPool.cursorAt mode (readerKind mode (roleLayout mode request)) request.origin index)) (role : Reader) :
    AlignedPool.Facts mode (readerKind mode (roleLayout mode request)) (readerCursor mode (roleLayout mode request) role)
      request.origin (gridBase mode request) (readerValue mode (roleLayout mode request) role)
      (whole mode request reference blocks) values := by
  have built := RoleInitialization.reader_initialized mode (roleLayout mode request) request.origin []
    (guardPieces mode request reference .base ++ guardPieces mode request reference .offset ++
      SpacedPacking.adjacent mode (KernelPackets.flatten (KernelPackets.programSegments mode blocks)) ++
      backedge mode request ++ reserve request.hostSpan (fieldPieces mode (roleLayout mode request))) values rfl fits role
  simpa only [whole, body, controlPrefix, List.append_assoc, List.nil_append, roleLayout] using built

/-- Every one of the thirteen metadata roles has its literal initial value,
code ownership, word alignment and owner placement in the complete byte image. -/
theorem field_initialized (mode : Mode) (request : Request) (reference : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) (endPC : Word mode) (values : Nat -> Word mode)
    (compiled : KernelImage.compile mode (roles mode request reference) (kernelStart mode request)
      Dolan.Mov.kernelProgram = some (blocks, endPC))
    (fits : forall index, index < 13 -> AlignedPool.Fits mode .scalar
      (AlignedPool.cursorAt mode .scalar (metadataStart mode request) index)) (role : Field) :
    AlignedPool.Facts mode .scalar (fieldCursor mode (roleLayout mode request) role)
      request.origin (gridBase mode request) (fieldValue mode (roleLayout mode request) role)
      (whole mode request reference blocks) values := by
  let cursor := fieldCursor mode (roleLayout mode request) role
  let entry : Entry mode := ⟨AlignedPacking.scalarStart mode cursor, .owned (fieldValue mode (roleLayout mode request) role)⟩
  have localFacts := RoleInitialization.field_initialized mode (roleLayout mode request) (metadataStart mode request) [] [] values
    (by simp only [roleLayout, SpacedPacking.size, List.map_nil, List.sum_nil, Nat.add_zero])
    (by simpa only [roleLayout] using fits) role
  have within : Fragment.Within mode (AlignedPool.fragment mode .scalar cursor (fieldValue mode (roleLayout mode request) role))
      (SpacedPacking.place mode request.origin (whole mode request reference blocks)) := by
    apply Fragment.within_trans mode _ _ _ _ (metadata_within mode request reference blocks endPC compiled)
    simpa only [List.nil_append, List.append_nil, cursor] using localFacts.within
  have member : entry ∈ SpacedPacking.place mode request.origin (whole mode request reference blocks) := within entry (List.Mem.head _)
  have position : (AlignedPool.field mode .scalar cursor).toNat = entry.pc + moffsOperandOffset mode :=
    AlignedPacking.scalar_label_location mode cursor (fits role.index.val role.index.isLt)
  exact ⟨within, Or.inl ⟨entry, member, ⟨fieldValue mode (roleLayout mode request) role, rfl⟩, position⟩,
    Fragment.initialized_owned_word mode (whole mode request reference blocks) request.origin (gridBase mode request) values
      entry member _ (AlignedPool.field mode .scalar cursor) rfl position, localFacts.aligned⟩

end SmcTuring.Native.ImageInitialization

module
public import SmcTuring.Native.LayoutPass

public section

namespace SmcTuring.Native.EmittedImage

open ControlImage RoleInitialization LayoutPass

/-- Reserve an unfetched gap in the first packet's padding. No host instruction
is introduced into the pure control fragment. Its bytes remain backing bytes. -/
@[expose] def reserve {mode : Mode} (gap : Nat) : List (SpacedPacking.Piece mode) -> List (SpacedPacking.Piece mode)
  | [] => []
  | first :: rest => { first with padding := gap + first.padding } :: rest

theorem reserve_size (mode : Mode) (gap : Nat) (pieces : List (SpacedPacking.Piece mode)) (nonempty : pieces ≠ []) :
    SpacedPacking.size mode (reserve gap pieces) = gap + SpacedPacking.size mode pieces := by
  cases pieces with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest => simp only [reserve, SpacedPacking.size, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem reserve_place (mode : Mode) (start gap : Nat) (pieces : List (SpacedPacking.Piece mode)) :
    SpacedPacking.place mode start (reserve gap pieces) = SpacedPacking.place mode (start + gap) pieces := by
  cases pieces with
  | nil => rfl
  | cons first rest => simp only [reserve, SpacedPacking.place, Nat.add_assoc]

@[expose] def body (mode : Mode) (request : Request) (reference : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) : List (SpacedPacking.Piece mode) :=
  controlPrefix mode request reference ++
    SpacedPacking.adjacent mode (KernelPackets.flatten (KernelPackets.programSegments mode blocks)) ++ backedge mode request
@[expose] def whole (mode : Mode) (request : Request) (reference : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) : List (SpacedPacking.Piece mode) :=
  body mode request reference blocks ++ reserve request.hostSpan (fieldPieces mode (roleLayout mode request))

private theorem fields_nonempty (mode : Mode) (request : Request) : fieldPieces mode (roleLayout mode request) ≠ [] := by
  simp [fieldPieces, fieldPayloads, fields, AlignedPool.pool, AlignedPool.pieces, AlignedTemplates.scalarPieces, AlignedTemplates.padded]

theorem body_extent (mode : Mode) (request : Request) (reference : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode (roles mode request reference) (kernelStart mode request)
      Dolan.Mov.kernelProgram = some (blocks, endPC)) :
    request.origin + SpacedPacking.size mode (body mode request reference blocks) = boundaryStart mode request := by
  rw [body, SpacedPacking.size_append, ←Nat.add_assoc, LayoutPass.body_extent mode request reference blocks endPC compiled, backedge_extent]

/-- The complete finite control/metadata image is a literal constructor. Its
final extent is the computed metadata limit, including the observation gap. -/
theorem whole_extent (mode : Mode) (request : Request) (reference : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode (roles mode request reference) (kernelStart mode request)
      Dolan.Mov.kernelProgram = some (blocks, endPC)) :
    request.origin + SpacedPacking.size mode (whole mode request reference blocks) = metadataLimit mode request := by
  rw [whole, SpacedPacking.size_append, ←Nat.add_assoc, body_extent mode request reference blocks endPC compiled,
    reserve_size mode request.hostSpan _ (fields_nonempty mode request), ←Nat.add_assoc, ←metadataStart, field_extent]

theorem grid_gap (mode : Mode) (request : Request) :
    metadataLimit mode request <= gridBase mode request - moffsOperandOffset mode := by
  cases mode <;> simp only [gridBase, Mode.stride, Mode.wordBytes, moffsOperandOffset, wordPrefix,
    List.length_cons, List.length_nil] <;> omega

theorem grid_enough (mode : Mode) (request : Request) : moffsOperandOffset mode <= gridBase mode request := by
  cases mode <;> simp only [gridBase, Mode.stride, Mode.wordBytes, moffsOperandOffset, wordPrefix,
    List.length_cons, List.length_nil] <;> omega

theorem initially_intact (mode : Mode) (request : Request) (reference : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) (endPC : Word mode) (values : Nat -> Word mode)
    (compiled : KernelImage.compile mode (roles mode request reference) (kernelStart mode request)
      Dolan.Mov.kernelProgram = some (blocks, endPC)) :
    SpacedCombinedImage.Intact mode (whole mode request reference blocks) request.origin (gridBase mode request)
      (SpacedCombinedImage.image mode (whole mode request reference blocks) request.origin (gridBase mode request) values) := by
  apply SpacedCombinedImage.initially_intact _ _ _ _ _ (grid_enough mode request)
  rw [whole_extent mode request reference blocks endPC compiled]
  exact grid_gap mode request

/-- Actual initialized source words are encoded in the operand grid of this
constructed byte image. Finite physical capacity remains an explicit premise. -/
theorem initially_represented (mode : Mode) (request : Request) (reference : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) (endPC : Word mode) (source : Dolan.Mov.State)
    (compiled : KernelImage.compile mode (roles mode request reference) (kernelStart mode request)
      Dolan.Mov.kernelProgram = some (blocks, endPC))
    (capacity : SourceData.Capacity mode (gridBase mode request) request.cells) :
    SourceData.Rep mode (gridBase mode request) request.cells source
      (SpacedCombinedImage.image mode (whole mode request reference blocks) request.origin (gridBase mode request)
        (SourceData.initialValues mode (gridBase mode request) source)) := by
  apply SourceData.initial_rep _ _ _ _ _ _ capacity (grid_enough mode request)
  rw [whole_extent mode request reference blocks endPC compiled]
  exact grid_gap mode request

end SmcTuring.Native.EmittedImage

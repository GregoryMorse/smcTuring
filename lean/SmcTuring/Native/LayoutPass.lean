module
public import SmcTuring.Native.MetadataGeometry

public section

namespace SmcTuring.Native.LayoutPass

open ControlImage RoleInitialization

/-- Host observation occupies an unfetched gap after the pure backedge. Its
byte extent and terminal offset are inputs for later loaded-image comparison. -/
structure Request where
  origin : Nat
  hostSpan : Nat
  terminalOffset : Nat
  closed : Bool
  cells : Nat

@[expose] def readerLimit (mode : Mode) (request : Request) : Nat := AlignedPool.cursorAt mode (.reader 0 0) request.origin 23
@[expose] def baseGuardStart (mode : Mode) (request : Request) : Nat := AlignedPacking.readerStart mode (readerLimit mode request)
@[expose] def baseGuardLimit (mode : Mode) (request : Request) : Nat := baseGuardStart mode request + ByteLengths.guardSpan mode
@[expose] def offsetGuardStart (mode : Mode) (request : Request) : Nat := AlignedPacking.readerStart mode (baseGuardLimit mode request)
@[expose] def kernelStart (mode : Mode) (request : Request) : Nat := offsetGuardStart mode request + ByteLengths.guardSpan mode
@[expose] def backedgeStart (mode : Mode) (request : Request) : Nat := kernelStart mode request + ByteLengths.programSpan mode Dolan.Mov.kernelProgram
@[expose] def boundaryStart (mode : Mode) (request : Request) : Nat := backedgeStart mode request + CallsImage.totalSize mode (.indirect 0)
@[expose] def metadataStart (mode : Mode) (request : Request) : Nat := boundaryStart mode request + request.hostSpan
@[expose] def metadataLimit (mode : Mode) (request : Request) : Nat := AlignedPool.cursorAt mode .scalar (metadataStart mode request) 13
@[expose] def gridBase (mode : Mode) (request : Request) : Nat :=
  metadataLimit mode request + (mode.stride - metadataLimit mode request % mode.stride) % mode.stride + mode.stride
@[expose] def roleLayout (mode : Mode) (request : Request) : RoleInitialization.Layout :=
  ⟨request.origin, metadataStart mode request, gridBase mode request,
    boundaryStart mode request + request.terminalOffset,
    if request.closed then kernelStart mode request else boundaryStart mode request⟩

@[expose] def guard (mode : Mode) (request : Request) (whole : List (SpacedPacking.Piece mode))
    (sense : GuardImage.Sense) : GuardImage.Layout mode :=
  let roles := roleLayout mode request
  { setup := {
      start := match sense with | .base => baseGuardStart mode request | .offset => offsetGuardStart mode request
      candidateCallee := readerPosition mode roles .candidate
      boundaryCallee := readerPosition mode roles .boundary
      top := fieldPosition mode roles .top
      slot := fieldPosition mode roles .slot
      resume := fieldPosition mode roles .resume
      scratch := fieldPosition mode roles .scratch
      candidate := fieldPosition mode roles .candidate
      boundary := fieldPosition mode roles .boundary
      origin := request.origin
      gridBase := gridBase mode request
      whole := whole
      captureInitial := Arithmetic.encodeNat mode (fieldPosition mode roles .slot)
      candidateInitial := readerValue mode roles .candidate
      boundaryInitial := readerValue mode roles .boundary }
    sense := sense
    zero := fieldPosition mode roles .zero
    mask := fieldPosition mode roles .mask
    selected := fieldPosition mode roles .selected
    terminal := fieldPosition mode roles .terminal
    zeroCallee := readerPosition mode roles .zero
    resumeCallee := readerPosition mode roles .resume
    terminalCallee := readerPosition mode roles .terminal
    maskCallee := readerPosition mode roles .mask
    zeroInitial := readerValue mode roles .zero
    resumeInitial := readerValue mode roles .resume
    terminalInitial := readerValue mode roles .terminal
    maskInitial := readerValue mode roles .mask }

@[expose] def roles (mode : Mode) (request : Request) (whole : List (SpacedPacking.Piece mode)) : KernelImage.Roles mode :=
  let layout := roleLayout mode request
  ⟨guard mode request whole .offset, request.cells, baseGuardStart mode request,
    readerPosition mode layout .pointer, readerPosition mode layout .pointerWord,
    fun register => readerPosition mode layout (.register register),
    fun choice => readerPosition mode layout (if choice then .offsetOne else .offsetZero),
    fun choice => fieldPosition mode layout (if choice then .offsetOne else .offsetZero)⟩

@[expose] def guardPieces (mode : Mode) (request : Request) (whole : List (SpacedPacking.Piece mode))
    (sense : GuardImage.Sense) : List (SpacedPacking.Piece mode) :=
  AlignedTemplates.padded mode (AlignedTemplates.readerPadding mode
    (match sense with | .base => readerLimit mode request | .offset => baseGuardLimit mode request))
    (GuardPackets.packets mode (guard mode request whole sense))
@[expose] def controlPrefix (mode : Mode) (request : Request) (whole : List (SpacedPacking.Piece mode)) : List (SpacedPacking.Piece mode) :=
  readerPieces mode (roleLayout mode request) ++ guardPieces mode request whole .base ++ guardPieces mode request whole .offset
@[expose] def backedge (mode : Mode) (request : Request) : List (SpacedPacking.Piece mode) :=
  SpacedPacking.adjacent mode (CallsImage.packets mode (backedgeStart mode request)
    (fieldPosition mode (roleLayout mode request) .top) (.indirect (fieldPosition mode (roleLayout mode request) .loop)))

theorem reader_extent (mode : Mode) (request : Request) :
    request.origin + SpacedPacking.size mode (readerPieces mode (roleLayout mode request)) = readerLimit mode request := by
  rw [readerPieces]
  change request.origin + SpacedPacking.size mode (AlignedPool.pool mode (readerKind mode (roleLayout mode request)) request.origin (readerPayloads mode (roleLayout mode request))) = _
  rw [AlignedPool.pool_extent, AlignedPool.end_cursor]
  simp only [readerPayloads, List.length_map, reader_count, roleLayout]
  exact AlignedPool.reader_cursor mode _ _ _ _

theorem field_extent (mode : Mode) (request : Request) :
    metadataStart mode request + SpacedPacking.size mode (fieldPieces mode (roleLayout mode request)) = metadataLimit mode request := by
  rw [fieldPieces]
  change metadataStart mode request + SpacedPacking.size mode (AlignedPool.pool mode .scalar (metadataStart mode request) (fieldPayloads mode (roleLayout mode request))) = _
  rw [AlignedPool.pool_extent, AlignedPool.end_cursor]
  simp only [fieldPayloads, List.length_map, field_count, roleLayout, metadataLimit]

theorem guard_extent (mode : Mode) (request : Request) (whole : List (SpacedPacking.Piece mode)) (sense : GuardImage.Sense) :
    (match sense with | .base => readerLimit mode request | .offset => baseGuardLimit mode request) +
      SpacedPacking.size mode (guardPieces mode request whole sense) =
      (guard mode request whole sense).setup.start + ByteLengths.guardSpan mode := by
  have nonempty : GuardPackets.packets mode (guard mode request whole sense) ≠ [] := by
    intro empty
    have count := GuardPackets.packet_count mode (guard mode request whole sense)
    rw [empty] at count
    contradiction
  unfold guardPieces
  rw [AlignedTemplates.padded_size mode _ _ nonempty, ByteLengths.guard_size]
  cases sense <;> simp only [guard, baseGuardStart, offsetGuardStart, AlignedTemplates.readerPadding,
    AlignedPacking.readerStart, Nat.add_assoc]

/-- The exact 23-reader and two-guard prefix reaches the computed source entry.
Every role address was resolved from byte geometry before source execution. -/
theorem prefix_extent (mode : Mode) (request : Request) (whole : List (SpacedPacking.Piece mode)) :
    request.origin + SpacedPacking.size mode (controlPrefix mode request whole) = kernelStart mode request := by
  have baseExtent := guard_extent mode request whole .base
  have offsetExtent := guard_extent mode request whole .offset
  change readerLimit mode request + SpacedPacking.size mode (guardPieces mode request whole .base) = baseGuardLimit mode request at baseExtent
  change baseGuardLimit mode request + SpacedPacking.size mode (guardPieces mode request whole .offset) = kernelStart mode request at offsetExtent
  rw [controlPrefix, SpacedPacking.size_append, SpacedPacking.size_append, ←Nat.add_assoc, ←Nat.add_assoc, reader_extent, baseExtent, offsetExtent]

theorem compiled_extent (mode : Mode) (request : Request) (whole : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode (roles mode request whole) (kernelStart mode request)
      Dolan.Mov.kernelProgram = some (blocks, endPC))
    (fits : backedgeStart mode request < 2 ^ (8 * mode.wordBytes)) :
    endPC.toNat = backedgeStart mode request ∧
      (forall block, block ∈ blocks -> KernelPackets.endPosition mode block < 2 ^ (8 * mode.wordBytes)) :=
  ByteLengths.compile_extent mode _ _ _ _ _ compiled fits

theorem body_extent (mode : Mode) (request : Request) (whole : List (SpacedPacking.Piece mode))
    (blocks : List (BlockImage.Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode (roles mode request whole) (kernelStart mode request)
      Dolan.Mov.kernelProgram = some (blocks, endPC)) :
    request.origin + SpacedPacking.size mode (controlPrefix mode request whole ++
      SpacedPacking.adjacent mode (KernelPackets.flatten (KernelPackets.programSegments mode blocks))) = backedgeStart mode request := by
  rw [SpacedPacking.size_append, ←Nat.add_assoc, prefix_extent, SpacedPacking.adjacent_size,
    ByteLengths.program_size, (KernelImage.compile_properties mode _ _ _ _ _ compiled).1]
  rfl

theorem backedge_extent (mode : Mode) (request : Request) :
    backedgeStart mode request + SpacedPacking.size mode (backedge mode request) = boundaryStart mode request := by
  rw [backedge, SpacedPacking.adjacent_size, CallsImage.packet_size]
  rfl

theorem grid_aligned (mode : Mode) (request : Request) : gridBase mode request % mode.stride = 0 := by
  cases mode <;> simp only [gridBase, Mode.stride, Mode.wordBytes] <;> omega

end SmcTuring.Native.LayoutPass

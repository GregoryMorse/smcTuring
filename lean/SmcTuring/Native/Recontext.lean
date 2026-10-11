module
public import SmcTuring.Native.ImageInitialization

public section

namespace SmcTuring.Native.Recontext

open BlockImage ControlImage

@[expose] def guard {mode : Mode} (layout : GuardImage.Layout mode) (whole : List (SpacedPacking.Piece mode)) : GuardImage.Layout mode :=
  { layout with setup := { layout.setup with whole := whole } }
@[expose] def address {mode : Mode} (layout : AddressImage.Layout mode) (whole : List (SpacedPacking.Piece mode)) : AddressImage.Layout mode :=
  { layout with offset := { layout.offset with guard := guard layout.offset.guard whole } }
@[expose] def block (mode : Mode) (whole : List (SpacedPacking.Piece mode)) : Block mode -> Block mode
  | .immediate layout => .immediate { layout with unit := { layout.unit with reader := { layout.unit.reader with whole := whole } } }
  | .load layout => .load { layout with address := address layout.address whole }
  | .store layout => .store { layout with address := address layout.address whole }
@[expose] def roles {mode : Mode} (layout : KernelImage.Roles mode) (whole : List (SpacedPacking.Piece mode)) : KernelImage.Roles mode :=
  { layout with guard := guard layout.guard whole }

theorem block_instruction (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (original : Block mode) :
    instruction (block mode whole original) = instruction original := by cases original <;> rfl

theorem block_start (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (original : Block mode) :
    start mode (block mode whole original) = start mode original := by cases original <;> rfl

theorem block_continuation (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (original : Block mode) :
    continuation mode (block mode whole original) = continuation mode original := by cases original <;> rfl

theorem block_context (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (original : Block mode) :
    context mode (block mode whole original) = { context mode original with whole := whole } := by cases original <;> rfl

/-- Replacing the proof context changes no emitted byte, position, or operand. -/
theorem block_segments (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (original : Block mode) :
    KernelPackets.segments mode (block mode whole original) = KernelPackets.segments mode original := by
  cases mode <;> cases original <;>
    simp only [block, address, guard, KernelPackets.segments, KernelPackets.addressSegments,
      KernelPackets.readScalar, KernelPackets.readCall, KernelPackets.guardCall, KernelPackets.storeCall,
      KernelPackets.scalar, ScalarImage.form, ScalarImage.displacement,
      OffsetGuardImage.readLayout, OffsetGuardImage.guardLayout, AddressImage.pointerLayout,
      AddressImage.baseGuard, AddressImage.guardLayout, PointerImage.baseLayout,
      PointerImage.offsetLayout, PointerImage.wordLayout, LoadImage.readLayout,
      StoreImage.readLayout, StoreImage.storeLayout, ReadScalarImage.scalarLayout,
      ReadScalarImage.endPosition, ReadScalarImage.scalarStart, AddressImage.pointerStart,
      AddressImage.pointerPosition, PointerImage.endPosition, LoadImage.readStart, StoreImage.readStart,
      StoreInvocationImage.entryPC, StoreInvocationImage.calleeLayout, StoreCalleeImage.entryPC]


theorem program_segments (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (original : List (Block mode)) :
    KernelPackets.programSegments mode (original.map (block mode whole)) = KernelPackets.programSegments mode original := by
  induction original with
  | nil => rfl
  | cons first rest ih =>
    change KernelPackets.segments mode (block mode whole first) ++ KernelPackets.programSegments mode (rest.map (block mode whole)) = _
    rw [block_segments, ih]
    rfl

theorem lower (mode : Mode) (layout : KernelImage.Roles mode) (whole : List (SpacedPacking.Piece mode))
    (position : Nat) (source : Dolan.Mov.Instruction) :
    KernelImage.lower mode (roles layout whole) position source =
      (KernelImage.lower mode layout position source).map (block mode whole) := by
  cases source with
  | immediate destination value => cases value <;> rfl
  | load destination base offset => rfl
  | store base offset source => rfl

/-- Compilation can be reattached to the final constructed image while keeping
all instruction bytes, source operands, physical positions and end PC. -/
theorem compile (mode : Mode) (layout : KernelImage.Roles mode) (whole : List (SpacedPacking.Piece mode))
    (position : Nat) (source : List Dolan.Mov.Instruction) (blocks : List (Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode layout position source = some (blocks, endPC)) :
    KernelImage.compile mode (roles layout whole) position source = some (blocks.map (block mode whole), endPC) := by
  induction source generalizing position blocks endPC with
  | nil =>
    simp only [KernelImage.compile, Option.some.injEq, Prod.mk.injEq] at compiled
    rcases compiled with ⟨rfl, rfl⟩
    rfl
  | cons source rest ih =>
    cases first : KernelImage.lower mode layout position source with
    | none => simp only [KernelImage.compile, first, Option.bind_none, reduceCtorEq] at compiled
    | some current =>
      cases later : KernelImage.compile mode layout (continuation mode current).toNat rest with
      | none => simp only [KernelImage.compile, first, Option.bind_some, later, Option.map_none, reduceCtorEq] at compiled
      | some result =>
        rcases result with ⟨tail, tailEnd⟩
        simp only [KernelImage.compile, first, Option.bind_some, later, Option.map_some, Option.some.injEq, Prod.mk.injEq] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        have moved := ih _ tail tailEnd later
        simp only [KernelImage.compile, lower, first, Option.map_some, Option.bind_some, block_continuation, moved, Option.map_some, List.map_cons]

theorem layout_roles (mode : Mode) (request : LayoutPass.Request) (first second : List (SpacedPacking.Piece mode)) :
    LayoutPass.roles mode request second = roles (LayoutPass.roles mode request first) second := rfl

theorem guard_packets (mode : Mode) (layout : GuardImage.Layout mode) (whole : List (SpacedPacking.Piece mode)) :
    GuardPackets.packets mode (guard layout whole) = GuardPackets.packets mode layout := by cases mode <;> rfl

private theorem layout_guard (mode : Mode) (request : LayoutPass.Request)
    (first second : List (SpacedPacking.Piece mode)) (sense : GuardImage.Sense) :
    LayoutPass.guard mode request second sense = guard (LayoutPass.guard mode request first sense) second := rfl

theorem layout_prefix (mode : Mode) (request : LayoutPass.Request) (first second : List (SpacedPacking.Piece mode)) :
    LayoutPass.controlPrefix mode request second = LayoutPass.controlPrefix mode request first := by
  simp only [LayoutPass.controlPrefix, LayoutPass.guardPieces, layout_guard mode request first second, guard_packets]

theorem emitted_image (mode : Mode) (request : LayoutPass.Request) (first second : List (SpacedPacking.Piece mode)) (original : List (Block mode)) :
    EmittedImage.whole mode request second (original.map (block mode second)) = EmittedImage.whole mode request first original := by
  simp only [EmittedImage.whole, EmittedImage.body, layout_prefix mode request first second, program_segments]

/-- The native kernel has an actual constructed image, not a cyclic assumed
context. All sixty-four blocks are compiled against exactly that same image. -/
theorem constructed_kernel (mode : Mode) (request : LayoutPass.Request) :
    exists whole blocks endPC,
      KernelImage.compile mode (LayoutPass.roles mode request whole) (LayoutPass.kernelStart mode request)
        Dolan.Mov.kernelProgram = some (blocks, endPC) ∧
      whole = EmittedImage.whole mode request whole blocks ∧
      blocks.map instruction = Dolan.Mov.kernelProgram ∧ blocks.length = 64 ∧
      ProgramImage.entry mode blocks endPC = Arithmetic.encodeNat mode (LayoutPass.kernelStart mode request) ∧
      ProgramImage.Linked mode blocks endPC ∧
      (forall current, current ∈ blocks -> (context mode current).whole = whole) := by
  rcases KernelImage.fixed_kernel mode (LayoutPass.roles mode request []) (LayoutPass.kernelStart mode request) with
    ⟨original, endPC, compiled, _⟩
  let whole := EmittedImage.whole mode request [] original
  let blocks := original.map (block mode whole)
  have moved : KernelImage.compile mode (LayoutPass.roles mode request whole) (LayoutPass.kernelStart mode request)
      Dolan.Mov.kernelProgram = some (blocks, endPC) := by
    rw [layout_roles mode request [] whole]
    exact compile mode _ whole _ _ _ _ compiled
  have actual := KernelImage.compile_properties mode _ _ _ blocks endPC moved
  have same : whole = EmittedImage.whole mode request whole blocks := (emitted_image mode request [] whole original).symm
  have length : blocks.length = 64 := by
    have lengths := congrArg List.length actual.1
    simpa only [List.length_map, Dolan.Mov.kernel_length] using lengths
  refine ⟨whole, blocks, endPC, moved, same, actual.1, length, actual.2.1, actual.2.2.1, ?_⟩
  intro current member
  rw [actual.2.2.2 current member]
  rfl

end SmcTuring.Native.Recontext

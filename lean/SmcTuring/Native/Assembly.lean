module
public import SmcTuring.Native.BoundedInitialization
public import SmcTuring.Native.Recontext

public section

namespace SmcTuring.Native.Assembly

open ControlImage RoleInitialization LayoutPass

/-- An actual finite assembly with static capacity and a proved image/context
identity. Initial Ready and future execution are deliberately absent. -/
structure Image (mode : Mode) (request : Request) extends BoundedInitialization.Input mode request where
  consistent : reference = EmittedImage.whole mode request reference blocks

@[expose] def control (mode : Mode) (request : Request) (assembly : Image mode request) : List (SpacedPacking.Piece mode) :=
  BoundedInitialization.image mode request assembly.toInput
@[expose] def context (mode : Mode) (request : Request) (assembly : Image mode request) : BlockImage.Context mode :=
  ⟨control mode request assembly, request.origin, gridBase mode request, request.cells,
    fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot⟩
@[expose] def initial (mode : Mode) (request : Request) (assembly : Image mode request) (source : Dolan.Mov.State)
    (accumulator stack : Word mode) (carry : Bool) : Execution.State mode :=
  ⟨Arithmetic.encodeNat mode (kernelStart mode request), accumulator, stack, carry,
    BoundedInitialization.memory mode request assembly.toInput (SourceData.initialValues mode (gridBase mode request) source)⟩

theorem exists_image (mode : Mode) (request : Request) (capacity : SourceData.Capacity mode (gridBase mode request) request.cells) :
    Nonempty (Image mode request) := by
  rcases Recontext.constructed_kernel mode request with ⟨whole, blocks, endPC, compiled, same, _⟩
  exact ⟨⟨⟨whole, blocks, endPC, compiled, capacity⟩, same⟩⟩

theorem common_context (mode : Mode) (request : Request) (assembly : Image mode request)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) :
    BlockImage.context mode block = context mode request assembly := by
  have common := (KernelImage.compile_properties mode _ _ _ _ _ assembly.compiled).2.2.2 block member
  rw [common]
  change ⟨assembly.reference, request.origin, gridBase mode request, request.cells,
    fieldPosition mode (roleLayout mode request) .top, fieldPosition mode (roleLayout mode request) .slot⟩ = context mode request assembly
  rw [assembly.consistent]
  rfl

theorem boundary_bound (mode : Mode) (request : Request) (assembly : Image mode request) :
    boundaryStart mode request <= metadataLimit mode request := by
  have body := EmittedImage.body_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled
  have all := EmittedImage.whole_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled
  simp only [EmittedImage.whole, SpacedPacking.size_append] at all
  omega

theorem backedge_fits (mode : Mode) (request : Request) (assembly : Image mode request) :
    backedgeStart mode request < 2 ^ (8 * mode.wordBytes) := by
  have full := BoundedInitialization.metadata_fits mode request assembly.toInput
  have bound := boundary_bound mode request assembly
  have before : backedgeStart mode request <= boundaryStart mode request := Nat.le_add_right _ _
  omega

theorem compiled_bounds (mode : Mode) (request : Request) (assembly : Image mode request) :
    assembly.endPC.toNat = backedgeStart mode request ∧
      (forall block, block ∈ assembly.blocks -> KernelPackets.endPosition mode block < 2 ^ (8 * mode.wordBytes)) :=
  LayoutPass.compiled_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled (backedge_fits mode request assembly)

private theorem kernel_fits (mode : Mode) (request : Request) (assembly : Image mode request) :
    kernelStart mode request < 2 ^ (8 * mode.wordBytes) :=
  Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (backedge_fits mode request assembly)

/-- All actual source snippets belong to the complete image used by their
execution contexts. Both placement and no-wrap are derived from construction. -/
theorem source_segment_within (mode : Mode) (request : Request) (assembly : Image mode request)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks)
    (segment : KernelPackets.Segment mode) (included : segment ∈ KernelPackets.segments mode block) :
    Fragment.Within mode (ControlPacking.place mode segment.start segment.packets)
      (SpacedPacking.place mode request.origin (control mode request assembly)) := by
  have placed := KernelPackets.global_placement mode (roles mode request assembly.reference) (kernelStart mode request)
    Dolan.Mov.kernelProgram assembly.blocks assembly.endPC assembly.compiled (kernel_fits mode request assembly)
    (compiled_bounds mode request assembly).2 request.origin (controlPrefix mode request assembly.reference)
    (backedge mode request ++ EmittedImage.reserve request.hostSpan (fieldPieces mode (roleLayout mode request)))
    (LayoutPass.prefix_extent mode request assembly.reference).symm block member segment included
  simpa only [control, BoundedInitialization.image, EmittedImage.whole, EmittedImage.body, List.append_assoc] using placed

theorem source_read_scalar_within (mode : Mode) (request : Request) (assembly : Image mode request)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode)
    (included : KernelPackets.readScalar mode op layout ∈ KernelPackets.segments mode block) :
    Fragment.Within mode (ControlPacking.place mode layout.reader.caller (CallsImage.packets mode layout.reader.caller layout.reader.top (.relative layout.reader.callee)))
      (SpacedPacking.place mode request.origin (control mode request assembly)) ∧
      ScalarImage.entry mode op (ReadScalarImage.scalarLayout mode layout) ∈ SpacedPacking.place mode request.origin (control mode request assembly) := by
  have placed := KernelPackets.global_read_scalar mode (roles mode request assembly.reference) (kernelStart mode request)
    Dolan.Mov.kernelProgram assembly.blocks assembly.endPC assembly.compiled (kernel_fits mode request assembly)
    (compiled_bounds mode request assembly).2 request.origin (controlPrefix mode request assembly.reference)
    (backedge mode request ++ EmittedImage.reserve request.hostSpan (fieldPieces mode (roleLayout mode request)))
    (LayoutPass.prefix_extent mode request assembly.reference).symm block member op layout included
  simpa only [control, BoundedInitialization.image, EmittedImage.whole, EmittedImage.body, List.append_assoc] using placed

theorem initially_intact (mode : Mode) (request : Request) (assembly : Image mode request) (source : Dolan.Mov.State)
    (accumulator stack : Word mode) (carry : Bool) :
    ProgramImage.intact mode (context mode request assembly) (initial mode request assembly source accumulator stack carry) :=
  EmittedImage.initially_intact mode request assembly.reference assembly.blocks assembly.endPC
    (SourceData.initialValues mode (gridBase mode request) source) assembly.compiled

theorem initially_represented (mode : Mode) (request : Request) (assembly : Image mode request) (source : Dolan.Mov.State)
    (accumulator stack : Word mode) (carry : Bool) :
    ProgramImage.represented mode (context mode request assembly) source (initial mode request assembly source accumulator stack carry) :=
  EmittedImage.initially_represented mode request assembly.reference assembly.blocks assembly.endPC source assembly.compiled assembly.capacity

end SmcTuring.Native.Assembly

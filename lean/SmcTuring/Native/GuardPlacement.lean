module
public import SmcTuring.Native.Assembly

public section

namespace SmcTuring.Native.GuardPlacement

open ControlImage RoleInitialization LayoutPass

@[expose] def guard (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (sense : GuardImage.Sense) : GuardImage.Layout mode :=
  LayoutPass.guard mode request assembly.reference sense
@[expose] def cursor (mode : Mode) (request : Request) : GuardImage.Sense -> Nat
  | .base => readerLimit mode request | .offset => baseGuardLimit mode request

private theorem position (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (sense : GuardImage.Sense) :
    (guard mode request assembly sense).setup.start = cursor mode request sense + AlignedTemplates.readerPadding mode (cursor mode request sense) := by
  cases sense <;> simp only [guard, LayoutPass.guard, cursor, baseGuardStart, offsetGuardStart,
    AlignedPacking.readerStart, AlignedTemplates.readerPadding, Nat.add_assoc]

/-- Both complete guards occupy their derived aligned positions in the actual
image shared by the compiled source blocks. -/
theorem guard_within (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (sense : GuardImage.Sense) :
    Fragment.Within mode (ControlPacking.place mode (guard mode request assembly sense).setup.start
      (GuardPackets.packets mode (guard mode request assembly sense)))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) := by
  let tail := SpacedPacking.adjacent mode (KernelPackets.flatten (KernelPackets.programSegments mode assembly.blocks)) ++
    backedge mode request ++ EmittedImage.reserve request.hostSpan (fieldPieces mode (roleLayout mode request))
  cases sense with
  | base =>
    have made := AlignedTemplates.padded_within mode request.origin (readerLimit mode request)
      (AlignedTemplates.readerPadding mode (readerLimit mode request)) (GuardPackets.packets mode (guard mode request assembly .base))
      (readerPieces mode (roleLayout mode request)) (guardPieces mode request assembly.reference .offset ++ tail)
      (LayoutPass.reader_extent mode request).symm
    have start := position mode request assembly .base
    change (guard mode request assembly .base).setup.start = readerLimit mode request + AlignedTemplates.readerPadding mode (readerLimit mode request) at start
    rw [←start] at made
    simpa only [Assembly.control, BoundedInitialization.image, EmittedImage.whole, EmittedImage.body, controlPrefix,
      guardPieces, guard, tail, List.append_assoc] using made
  | offset =>
    have readerExtent := LayoutPass.reader_extent mode request
    have baseExtent := LayoutPass.guard_extent mode request assembly.reference .base
    change readerLimit mode request + SpacedPacking.size mode (guardPieces mode request assembly.reference .base) = baseGuardLimit mode request at baseExtent
    have location : baseGuardLimit mode request = request.origin + SpacedPacking.size mode
        (readerPieces mode (roleLayout mode request) ++ guardPieces mode request assembly.reference .base) := by
      rw [SpacedPacking.size_append, ←Nat.add_assoc, readerExtent, baseExtent]
    have made := AlignedTemplates.padded_within mode request.origin (baseGuardLimit mode request)
      (AlignedTemplates.readerPadding mode (baseGuardLimit mode request)) (GuardPackets.packets mode (guard mode request assembly .offset))
      (readerPieces mode (roleLayout mode request) ++ guardPieces mode request assembly.reference .base) tail location
    have start := position mode request assembly .offset
    change (guard mode request assembly .offset).setup.start = baseGuardLimit mode request + AlignedTemplates.readerPadding mode (baseGuardLimit mode request) at start
    rw [←start] at made
    simpa only [Assembly.control, BoundedInitialization.image, EmittedImage.whole, EmittedImage.body, controlPrefix,
      guardPieces, guard, tail, List.append_assoc] using made

theorem segment_within (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (sense : GuardImage.Sense)
    (segment : KernelPackets.Segment mode) (member : segment ∈ GuardPackets.segments mode (guard mode request assembly sense)) :
    Fragment.Within mode (ControlPacking.place mode segment.start segment.packets)
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) :=
  Fragment.within_trans mode _ _ _
    (KernelPackets.ordered_placement mode _ _ _ (GuardPackets.ordered mode (guard mode request assembly sense)) segment member)
    (guard_within mode request assembly sense)

theorem read_scalar_within (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (sense : GuardImage.Sense)
    (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode)
    (member : KernelPackets.readScalar mode op layout ∈ GuardPackets.segments mode (guard mode request assembly sense)) :
    Fragment.Within mode (ControlPacking.place mode layout.reader.caller (CallsImage.packets mode layout.reader.caller layout.reader.top (.relative layout.reader.callee)))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) ∧
      ScalarImage.entry mode op (ReadScalarImage.scalarLayout mode layout) ∈ SpacedPacking.place mode request.origin (Assembly.control mode request assembly) := by
  have enclosing := segment_within mode request assembly sense _ member
  have finer := KernelPackets.read_scalar_placement mode op layout
  constructor
  · exact Fragment.within_trans mode _ _ _ finer.1 enclosing
  · apply enclosing; apply finer.2; exact List.Mem.head _

theorem capture_within (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (sense : GuardImage.Sense) :
    Fragment.Within mode (ControlPacking.place mode (guard mode request assembly sense).setup.start
      (ReaderImage.packets mode (guard mode request assembly sense).setup.start (guard mode request assembly sense).setup.captureInitial))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) := by
  let layout := guard mode request assembly sense
  let capture : KernelPackets.Segment mode := ⟨layout.setup.start, ReaderImage.packets mode layout.setup.start layout.setup.captureInitial⟩
  have included : capture ∈ GuardPackets.segments mode layout :=
    List.mem_append_left _ (List.mem_append_left _ (List.Mem.head _))
  exact segment_within mode request assembly sense capture included

structure CaptureSpec (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (sense : GuardImage.Sense) (values : Nat -> Word mode) : Prop where
  fits : (guard mode request assembly sense).setup.start + ReaderImage.totalSize mode < 2 ^ (8 * mode.wordBytes)
  owned : BoundedInitialization.owned mode request assembly.toInput (ReaderImage.label mode (guard mode request assembly sense).setup.start)
  initialized : Execution.load mode (BoundedInitialization.memory mode request assembly.toInput values)
    (ReaderImage.label mode (guard mode request assembly sense).setup.start) = Arithmetic.encodeNat mode (fieldPosition mode (roleLayout mode request) .slot)
  aligned : (ReaderImage.label mode (guard mode request assembly sense).setup.start).toNat % mode.wordBytes = 0

/-- Each guard's capture is a code-owned aligned operand initialized from the
actual emitted bytes to the common return slot. Its whole-packet bound is derived. -/
theorem capture_constructed (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (sense : GuardImage.Sense)
    (values : Nat -> Word mode) : CaptureSpec mode request assembly sense values := by
  let layout := guard mode request assembly sense
  let entry := ReaderImage.lastEntry mode layout.setup.start layout.setup.captureInitial
  have within := capture_within mode request assembly sense
  have member : entry ∈ SpacedPacking.place mode request.origin (Assembly.control mode request assembly) := by
    apply within
    rw [ReaderImage.placed_roles]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have upper := SpacedPacking.placed_upper mode (Assembly.control mode request assembly) request.origin entry member
  rw [owned_packet_length mode entry layout.setup.captureInitial rfl] at upper
  have ending := EmittedImage.whole_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled
  change request.origin + SpacedPacking.size mode (Assembly.control mode request assembly) = metadataLimit mode request at ending
  rw [ending] at upper
  have capacity := BoundedInitialization.metadata_fits mode request assembly.toInput
  have fits : layout.setup.start + ReaderImage.totalSize mode < 2 ^ (8 * mode.wordBytes) := by
    change layout.setup.start + ReaderImage.prefixSize mode + (moffsOperandOffset mode + mode.wordBytes) <= metadataLimit mode request at upper
    cases mode <;> simp only [ReaderImage.prefixSize, ReaderImage.totalSize, moffsOperandOffset, wordPrefix, Mode.wordBytes,
      List.length_cons, List.length_nil] at * <;> omega
  have label := ReaderImage.label_location mode layout.setup.start layout.setup.captureInitial fits
  have initialized := Fragment.initialized_owned_word mode (Assembly.control mode request assembly) request.origin (gridBase mode request)
    values entry member layout.setup.captureInitial (ReaderImage.label mode layout.setup.start) rfl label
  have aligned : (ReaderImage.label mode layout.setup.start).toNat % mode.wordBytes = 0 := by
    have startPosition : layout.setup.start = AlignedPacking.readerStart mode (cursor mode request sense) := by
      rw [position]
      simp only [AlignedTemplates.readerPadding, AlignedPacking.readerStart, Nat.add_assoc]
    rw [startPosition]
    apply AlignedPacking.reader_label_aligned
    simpa only [startPosition] using fits
  exact ⟨fits, Or.inl (Fragment.owned_view mode _ _ _ within (ReaderImage.label_owned mode layout.setup.start layout.setup.captureInitial fits)),
    initialized, aligned⟩

end SmcTuring.Native.GuardPlacement

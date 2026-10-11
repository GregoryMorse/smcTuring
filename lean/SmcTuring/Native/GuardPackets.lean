module
public import SmcTuring.Native.KernelPackets

public section

namespace SmcTuring.Native.GuardPackets

open ControlImage KernelPackets

@[expose] def setupSegments (mode : Mode) (layout : GuardSetupImage.Layout mode) : List (Segment mode) :=
  [⟨layout.start, ReaderImage.packets mode layout.start layout.captureInitial⟩,
    scalar mode .store (GuardSetupImage.resumeLayout mode layout),
    readCall mode (GuardSetupImage.candidateLayout mode layout),
    scalar mode .store (GuardSetupImage.scratchLayout mode layout),
    readCall mode (GuardSetupImage.boundaryLayout mode layout)]
@[expose] def borrowSegments (mode : Mode) (layout : BorrowMaskImage.Layout mode) : List (Segment mode) :=
  [scalar mode .subtract (BorrowMaskImage.subLayout mode layout), readCall mode layout.reader,
    scalar mode .store (BorrowMaskImage.storeLayout mode layout), scalar mode .subtractBorrowZero (BorrowMaskImage.sbbLayout mode layout)]
@[expose] def selectionSegments (mode : Mode) (layout : GuardSelectionImage.Layout mode) : List (Segment mode) :=
  [readScalar mode .store (GuardSelectionImage.firstLayout mode layout),
    readScalar mode .bitXor (GuardSelectionImage.secondLayout mode layout),
    readScalar mode .bitAnd (GuardSelectionImage.thirdLayout mode layout),
    readScalar mode .bitXor (GuardSelectionImage.fourthLayout mode layout),
    ⟨GuardSelectionImage.callStart mode layout,
      CallsImage.packets mode (GuardSelectionImage.callStart mode layout) layout.top (.indirect layout.selected)⟩]
@[expose] def segments (mode : Mode) (layout : GuardImage.Layout mode) : List (Segment mode) :=
  setupSegments mode layout.setup ++ borrowSegments mode (GuardImage.borrowLayout mode layout) ++
    selectionSegments mode (GuardImage.selectionLayout mode layout)
@[expose] def endPosition (mode : Mode) (layout : GuardImage.Layout mode) : Nat :=
  GuardSelectionImage.callStart mode (GuardImage.selectionLayout mode layout) +
    CallsImage.totalSize mode (.indirect layout.selected)
@[expose] def packets (mode : Mode) (layout : GuardImage.Layout mode) : List (Packet mode) := flatten (segments mode layout)

private theorem scalar_start (mode : Mode) (op : ScalarImage.Op) (layout : ScalarImage.Layout mode) :
    (scalar mode op layout).start = layout.start := rfl
private theorem read_scalar_start (mode : Mode) (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode) :
    (readScalar mode op layout).start = layout.reader.caller := rfl

private theorem setup_ordered (mode : Mode) (layout : GuardSetupImage.Layout mode) :
    Ordered mode layout.start (setupSegments mode layout) (GuardSetupImage.endPosition mode layout) := by
  simp only [setupSegments, Ordered, scalar_start, readCall, CallsImage.packet_size, ReaderImage.packet_size, scalar_size,
    GuardSetupImage.resumeLayout, GuardSetupImage.candidateLayout, GuardSetupImage.scratchLayout,
    GuardSetupImage.boundaryLayout, GuardSetupImage.resumeStart, GuardSetupImage.candidateStart,
    GuardSetupImage.scratchStart, GuardSetupImage.boundaryStart, GuardSetupImage.endPosition, Nat.add_assoc]
  repeat' constructor

private theorem borrow_ordered (mode : Mode) (layout : BorrowMaskImage.Layout mode)
    (nextReader : layout.reader.caller = layout.start + ScalarImage.size mode .subtract) :
    Ordered mode layout.start (borrowSegments mode layout)
      (BorrowMaskImage.storeStart mode layout + ScalarImage.size mode .store + ScalarImage.size mode .subtractBorrowZero) := by
  simp only [borrowSegments, Ordered, scalar_start, readCall, CallsImage.packet_size, scalar_size,
    BorrowMaskImage.subLayout, BorrowMaskImage.storeLayout, BorrowMaskImage.sbbLayout, BorrowMaskImage.storeStart, nextReader, Nat.add_assoc]
  repeat' constructor

private theorem read_scalar_bytes (mode : Mode) (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode) :
    ControlPacking.size mode (readScalar mode op layout).packets =
      CallsImage.totalSize mode (.relative layout.reader.callee) + ScalarImage.size mode op := by
  apply Nat.add_left_cancel (n := layout.reader.caller)
  simpa only [ReadScalarImage.endPosition, ReadScalarImage.scalarStart, Nat.add_assoc] using read_scalar_size mode op layout

private theorem selection_ordered (mode : Mode) (layout : GuardSelectionImage.Layout mode) :
    Ordered mode layout.start (selectionSegments mode layout)
      (GuardSelectionImage.callStart mode layout + CallsImage.totalSize mode (.indirect layout.selected)) := by
  simp only [selectionSegments, Ordered, read_scalar_start, read_scalar_bytes, CallsImage.packet_size,
    GuardSelectionImage.firstLayout, GuardSelectionImage.secondLayout, GuardSelectionImage.thirdLayout,
    GuardSelectionImage.fourthLayout, GuardSelectionImage.updateLayout, GuardSelectionImage.callStart,
    ReadScalarImage.endPosition, ReadScalarImage.scalarStart, Nat.add_assoc]
  repeat' constructor

/-- The two guard orientations emit the same contiguous stage geometry. Their
reader targets differ, but all positions are derived from actual packet sizes. -/
theorem ordered (mode : Mode) (layout : GuardImage.Layout mode) :
    Ordered mode layout.setup.start (segments mode layout) (endPosition mode layout) := by
  exact ordered_append mode _ _ _ _ _
    (ordered_append mode _ _ _ _ _ (setup_ordered mode layout.setup)
      (borrow_ordered mode (GuardImage.borrowLayout mode layout) rfl))
    (selection_ordered mode (GuardImage.selectionLayout mode layout))

/-- Thirty-seven inline packets plus seven shared reader invocations give the
already proved 86-instruction fetched guard. Reader bodies are not duplicated. -/
theorem packet_count (mode : Mode) (layout : GuardImage.Layout mode) : (packets mode layout).length = 37 := by
  simp [packets, segments, setupSegments, borrowSegments, selectionSegments, flatten, readScalar, readCall, scalar,
    ReaderImage.packets, CallsImage.packets]

/-- Each physical guard fragment embeds in the constructed padded prefix. -/
theorem global_placement (mode : Mode) (layout : GuardImage.Layout mode) (origin : Nat)
    (leading trailing : List (SpacedPacking.Piece mode))
    (start : layout.setup.start = origin + SpacedPacking.size mode leading)
    (segment : Segment mode) (member : segment ∈ segments mode layout) :
    Fragment.Within mode (ControlPacking.place mode segment.start segment.packets)
      (SpacedPacking.place mode origin (leading ++ SpacedPacking.adjacent mode (packets mode layout) ++ trailing)) := by
  have localPlacement := ordered_placement mode (segments mode layout) layout.setup.start (endPosition mode layout)
    (ordered mode layout) segment member
  intro entry belongs
  have placed := localPlacement entry belongs
  rw [start] at placed
  exact SpacedPacking.adjacent_member mode origin leading trailing _ entry placed

end SmcTuring.Native.GuardPackets

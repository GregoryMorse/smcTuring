module
public import SmcTuring.Native.GuardPackets
public import SmcTuring.Native.AlignedPacking

public section

namespace SmcTuring.Native.AlignedTemplates

open ControlImage

@[expose] def padded (mode : Mode) (padding : Nat) : List (Packet mode) -> List (SpacedPacking.Piece mode)
  | [] => []
  | first :: rest => ⟨padding, first⟩ :: SpacedPacking.adjacent mode rest

theorem padded_size (mode : Mode) (padding : Nat) (packets : List (Packet mode)) (nonempty : packets ≠ []) :
    SpacedPacking.size mode (padded mode padding packets) = padding + ControlPacking.size mode packets := by
  cases packets with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
    simp only [padded, SpacedPacking.size, List.map_cons, List.sum_cons]
    rw [←SpacedPacking.size, SpacedPacking.adjacent_size]
    simp only [ControlPacking.size, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem padded_place (mode : Mode) (padding start : Nat) (packets : List (Packet mode)) :
    SpacedPacking.place mode start (padded mode padding packets) = ControlPacking.place mode (start + padding) packets := by
  cases packets with
  | nil => rfl
  | cons first rest =>
    simp only [padded, SpacedPacking.place, SpacedPacking.adjacent_place, ControlPacking.place]

/-- Padding is computed before the called entry, and no padding opcode is part
of the invocation. The packet fragment belongs to the whole image by append. -/
theorem padded_within (mode : Mode) (origin start padding : Nat) (packets : List (Packet mode))
    (leading trailing : List (SpacedPacking.Piece mode)) (location : start = origin + SpacedPacking.size mode leading) :
    Fragment.Within mode (ControlPacking.place mode (start + padding) packets)
      (SpacedPacking.place mode origin (leading ++ padded mode padding packets ++ trailing)) := by
  intro entry member
  rw [SpacedPacking.place_append, SpacedPacking.place_append, ←location, padded_place]
  exact List.mem_append_left _ (List.mem_append_right _ member)

@[expose] def readerPadding (mode : Mode) (cursor : Nat) : Nat := AlignedPacking.alignPadding mode cursor + AlignedPacking.readerExtra mode
@[expose] def readerPieces (mode : Mode) (cursor top slot : Nat) (initial : Word mode) : List (SpacedPacking.Piece mode) :=
  padded mode (readerPadding mode cursor)
    (ReadCalleeImage.packets mode (AlignedPacking.readerStart mode cursor) top slot initial)
@[expose] def readerEnd (mode : Mode) (cursor : Nat) : Nat := AlignedPacking.readerStart mode cursor + ReadCalleeImage.totalSize mode

@[expose] def scalarPadding (mode : Mode) (cursor : Nat) : Nat := AlignedPacking.alignPadding mode cursor + AlignedPacking.scalarExtra mode
@[expose] def scalarPieces (mode : Mode) (cursor : Nat) (initial : Word mode) : List (SpacedPacking.Piece mode) :=
  padded mode (scalarPadding mode cursor) [.owned initial]
@[expose] def scalarEnd (mode : Mode) (cursor : Nat) : Nat :=
  AlignedPacking.scalarStart mode cursor + instructionLength mode (.moffs 0)

theorem reader_extent (mode : Mode) (cursor top slot : Nat) (initial : Word mode) :
    cursor + SpacedPacking.size mode (readerPieces mode cursor top slot initial) = readerEnd mode cursor := by
  rw [readerPieces, padded_size mode _ _ (by simp [ReadCalleeImage.packets, ReaderImage.packets]), ReadCalleeImage.packet_size]
  simp only [readerEnd, readerPadding, AlignedPacking.readerStart, Nat.add_assoc]

theorem scalar_extent (mode : Mode) (cursor : Nat) (initial : Word mode) :
    cursor + SpacedPacking.size mode (scalarPieces mode cursor initial) = scalarEnd mode cursor := by
  rw [scalarPieces, padded_size mode _ _ (by simp)]
  simp only [ControlPacking.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Packet.bytes,
    instruction_length, scalarEnd, scalarPadding, AlignedPacking.scalarStart, instructionLength, Nat.add_assoc, Nat.add_zero]

structure ReaderSpec (mode : Mode) (cursor top slot origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode) : Prop where
  extent : cursor + SpacedPacking.size mode (readerPieces mode cursor top slot initial) = readerEnd mode cursor
  within : Fragment.Within mode
    (ControlPacking.place mode (AlignedPacking.readerStart mode cursor)
      (ReadCalleeImage.packets mode (AlignedPacking.readerStart mode cursor) top slot initial))
    (SpacedPacking.place mode origin whole)
  owned : SpacedCombinedImage.Owned mode whole origin gridBase (ReaderImage.label mode (AlignedPacking.readerStart mode cursor))
  initialized : Execution.load mode (SpacedCombinedImage.image mode whole origin gridBase values)
    (ReaderImage.label mode (AlignedPacking.readerStart mode cursor)) = initial
  aligned : (ReaderImage.label mode (AlignedPacking.readerStart mode cursor)).toNat % mode.wordBytes = 0

/-- The complete aligned seven-packet reader is emitted once. Its actual MOFFS
operand is owned, initialized to the supplied target, and word aligned. -/
theorem reader_constructed (mode : Mode) (cursor top slot origin gridBase : Nat) (initial : Word mode)
    (leading trailing : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode)
    (location : cursor = origin + SpacedPacking.size mode leading)
    (fits : readerEnd mode cursor < 2 ^ (8 * mode.wordBytes)) :
    ReaderSpec mode cursor top slot origin gridBase initial
      (leading ++ readerPieces mode cursor top slot initial ++ trailing) values := by
  let start := AlignedPacking.readerStart mode cursor
  let whole := leading ++ readerPieces mode cursor top slot initial ++ trailing
  have readerFits := ReadCalleeImage.reader_fits mode start fits
  have placed : Fragment.Within mode (ControlPacking.place mode start (ReadCalleeImage.packets mode start top slot initial))
      (SpacedPacking.place mode origin whole) := by
    simpa only [start, whole, readerPieces, readerPadding, AlignedPacking.readerStart, Nat.add_assoc] using
      padded_within mode origin cursor (readerPadding mode cursor)
        (ReadCalleeImage.packets mode start top slot initial) leading trailing location
  have readPlaced := Fragment.within_trans mode _ _ _ (ReadCalleeImage.reader_within mode start top slot initial) placed
  have lastMember : ReaderImage.lastEntry mode start initial ∈ SpacedPacking.place mode origin whole := by
    apply readPlaced
    rw [ReaderImage.placed_roles]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have labelLocation := ReaderImage.label_location mode start initial readerFits
  have initializer := Fragment.initialized_owned_word mode whole origin gridBase values
    (ReaderImage.lastEntry mode start initial) lastMember initial (ReaderImage.label mode start) rfl labelLocation
  have extent := reader_extent mode cursor top slot initial
  exact ⟨extent, placed, Or.inl (Fragment.owned_view mode _ _ _ readPlaced (ReaderImage.label_owned mode start initial readerFits)),
    initializer, AlignedPacking.reader_label_aligned mode cursor readerFits⟩

structure ScalarSpec (mode : Mode) (cursor origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode) : Prop where
  extent : cursor + SpacedPacking.size mode (scalarPieces mode cursor initial) = scalarEnd mode cursor
  within : Fragment.Within mode (ControlPacking.place mode (AlignedPacking.scalarStart mode cursor) [.owned initial])
    (SpacedPacking.place mode origin whole)
  owned : SpacedCombinedImage.Owned mode whole origin gridBase (AlignedPacking.scalarLabel mode cursor)
  initialized : Execution.load mode (SpacedCombinedImage.image mode whole origin gridBase values)
    (AlignedPacking.scalarLabel mode cursor) = initial
  aligned : (AlignedPacking.scalarLabel mode cursor).toNat % mode.wordBytes = 0

/-- Inactive storage is an actual encoded owned MOFFS instruction. Padding
aligns its operand, and the initialized value follows from the byte overlay. -/
theorem scalar_constructed (mode : Mode) (cursor origin gridBase : Nat) (initial : Word mode)
    (leading trailing : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode)
    (location : cursor = origin + SpacedPacking.size mode leading)
    (fits : AlignedPacking.scalarStart mode cursor + moffsOperandOffset mode < 2 ^ (8 * mode.wordBytes)) :
    ScalarSpec mode cursor origin gridBase initial (leading ++ scalarPieces mode cursor initial ++ trailing) values := by
  let whole := leading ++ scalarPieces mode cursor initial ++ trailing
  let entry : Entry mode := ⟨AlignedPacking.scalarStart mode cursor, .owned initial⟩
  have placed : Fragment.Within mode (ControlPacking.place mode (AlignedPacking.scalarStart mode cursor) [.owned initial])
      (SpacedPacking.place mode origin whole) := by
    simpa only [whole, scalarPieces, scalarPadding, AlignedPacking.scalarStart, Nat.add_assoc] using
      padded_within mode origin cursor (scalarPadding mode cursor) [.owned initial] leading trailing location
  have member : entry ∈ SpacedPacking.place mode origin whole := placed entry (List.Mem.head _)
  have field : (AlignedPacking.scalarLabel mode cursor).toNat = entry.pc + moffsOperandOffset mode :=
    AlignedPacking.scalar_label_location mode cursor fits
  have initializer := Fragment.initialized_owned_word mode whole origin gridBase values entry member initial
    (AlignedPacking.scalarLabel mode cursor) rfl field
  have extent := scalar_extent mode cursor initial
  exact ⟨extent, placed, Or.inl ⟨entry, member, ⟨initial, rfl⟩, field⟩,
    initializer, AlignedPacking.scalar_label_aligned mode cursor fits⟩

end SmcTuring.Native.AlignedTemplates

module
public import SmcTuring.Native.ControlPacking

public section

namespace SmcTuring.Native.SpacedPacking

open ControlImage

/-- Padding precedes a packet and is not an executed instruction. -/
structure Piece (mode : Mode) where
  padding : Nat
  packet : Packet mode
  deriving DecidableEq

@[expose] def size (mode : Mode) (pieces : List (Piece mode)) : Nat :=
  (pieces.map (fun piece => piece.padding + (piece.packet.bytes mode).length)).sum

@[expose] def place (mode : Mode) : Nat -> List (Piece mode) -> List (Entry mode)
  | _, [] => []
  | start, piece :: rest => { pc := start + piece.padding, packet := piece.packet } ::
      place mode (start + piece.padding + (piece.packet.bytes mode).length) rest

@[expose] def adjacent (mode : Mode) (packets : List (Packet mode)) : List (Piece mode) :=
  packets.map (fun packet => { padding := 0, packet := packet })

theorem adjacent_size (mode : Mode) (packets : List (Packet mode)) :
    size mode (adjacent mode packets) = ControlPacking.size mode packets := by
  simp [size, adjacent, ControlPacking.size, List.map_map, Function.comp_def]

theorem adjacent_place (mode : Mode) (packets : List (Packet mode)) (start : Nat) :
    place mode start (adjacent mode packets) = ControlPacking.place mode start packets := by
  induction packets generalizing start with
  | nil => rfl
  | cons packet rest ih =>
    change { pc := start, packet := packet } ::
      place mode (start + (packet.bytes mode).length) (adjacent mode rest) =
      { pc := start, packet := packet } :: ControlPacking.place mode (start + (packet.bytes mode).length) rest
    rw [ih]

theorem size_append (mode : Mode) (first second : List (Piece mode)) :
    size mode (first ++ second) = size mode first + size mode second := by simp [size]

theorem place_append (mode : Mode) (start : Nat) (first second : List (Piece mode)) :
    place mode start (first ++ second) = place mode start first ++ place mode (start + size mode first) second := by
  induction first generalizing start with
  | nil => simp [place, size]
  | cons head tail ih => simp [place, size, ih, Nat.add_assoc]

theorem placed_lower (mode : Mode) (pieces : List (Piece mode)) (start : Nat) (entry : Entry mode)
    (member : List.Mem entry (place mode start pieces)) : start <= entry.pc := by
  induction pieces generalizing start with
  | nil => cases member
  | cons piece rest ih =>
    change List.Mem entry ({ pc := start + piece.padding, packet := piece.packet } ::
      place mode (start + piece.padding + (piece.packet.bytes mode).length) rest) at member
    cases member with
    | head => exact Nat.le_add_right start _
    | tail _ next => exact Nat.le_trans (by omega) (ih _ next)

theorem placed_upper (mode : Mode) (pieces : List (Piece mode)) (start : Nat) (entry : Entry mode)
    (member : List.Mem entry (place mode start pieces)) :
    entry.pc + (entry.bytes mode).length <= start + size mode pieces := by
  induction pieces generalizing start with
  | nil => cases member
  | cons piece rest ih =>
    change List.Mem entry ({ pc := start + piece.padding, packet := piece.packet } ::
      place mode (start + piece.padding + (piece.packet.bytes mode).length) rest) at member
    cases member with
    | head => simp [size, Entry.bytes, Nat.add_assoc]
    | tail _ next => simpa [size, Nat.add_assoc] using ih _ next

theorem placed_separated (mode : Mode) (pieces : List (Piece mode)) (start : Nat) :
    Separated mode (place mode start pieces) := by
  induction pieces generalizing start with
  | nil => intro first member; cases member
  | cons piece rest ih =>
    intro first member second secondMember different
    change List.Mem first ({ pc := start + piece.padding, packet := piece.packet } ::
      place mode (start + piece.padding + (piece.packet.bytes mode).length) rest) at member
    change List.Mem second ({ pc := start + piece.padding, packet := piece.packet } ::
      place mode (start + piece.padding + (piece.packet.bytes mode).length) rest) at secondMember
    cases member with
    | head =>
      cases secondMember with
      | head => exact False.elim (different rfl)
      | tail _ next => exact Or.inl (placed_lower mode rest _ second next)
    | tail _ firstNext =>
      cases secondMember with
      | head => exact Or.inr (placed_lower mode rest _ first firstNext)
      | tail _ secondNext => exact ih _ first firstNext second secondNext different

theorem initial_packet (mode : Mode) (pieces : List (Piece mode)) (start : Nat) (memory : ByteMemory.Memory)
    (entry : Entry mode) (member : List.Mem entry (place mode start pieces)) :
    ByteMemory.bytesAt (image mode (place mode start pieces) memory) entry.pc (entry.bytes mode).length = entry.bytes mode :=
  image_packet mode _ memory (placed_separated mode pieces start) entry member

theorem initially_intact (mode : Mode) (pieces : List (Piece mode)) (start : Nat) (memory : ByteMemory.Memory) :
    Intact mode (place mode start pieces) (image mode (place mode start pieces) memory) :=
  initialized_intact mode _ memory (placed_separated mode pieces start)

theorem initial_fetch (mode : Mode) (pieces : List (Piece mode)) (start : Nat) (memory : ByteMemory.Memory)
    (entry : Entry mode) (member : List.Mem entry (place mode start pieces)) :
    Fetch.fetch mode (image mode (place mode start pieces) memory) entry.pc =
      some (currentForm mode entry (image mode (place mode start pieces) memory)) :=
  fetch_current mode entry _ (initially_intact mode pieces start memory entry member)

/-- Every byte outside the actual finite packet spans retains its backing value,
including alignment padding inside the fragment's overall extent. -/
theorem uncovered_frame (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory) (position : Nat)
    (uncovered : forall entry, List.Mem entry entries -> Not (ByteMemory.Inside entry.pc (entry.bytes mode).length position)) :
    image mode entries memory position = memory position := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    change ByteMemory.putBytes (image mode rest memory) entry.pc (entry.bytes mode) position = _
    rw [ByteMemory.put_frame _ _ _ position (uncovered entry (List.Mem.head rest))]
    exact ih (fun observed member => uncovered observed (List.Mem.tail entry member))

theorem image_frame (mode : Mode) (pieces : List (Piece mode)) (start : Nat) (memory : ByteMemory.Memory)
    (position : Nat) (outside : Or (position < start) (start + size mode pieces <= position)) :
    image mode (place mode start pieces) memory position = memory position := by
  apply uncovered_frame
  intro entry member
  have lower := placed_lower mode pieces start entry member
  have upper := placed_upper mode pieces start entry member
  rcases outside with before | after <;> unfold ByteMemory.Inside <;> omega

theorem above_external (mode : Mode) (pieces : List (Piece mode)) (start : Nat) (address : Word mode)
    (after : start + size mode pieces <= address.toNat) : External mode (place mode start pieces) address := by
  intro entry member index
  have bound := placed_upper mode pieces start entry member
  have small := index.isLt
  unfold ByteMemory.Inside
  omega

/-- Contiguous instruction bodies embed in a padded global sequence through
computed list append and placement, without a fetch premise. -/
theorem adjacent_member (mode : Mode) (start : Nat) (leading trailing : List (Piece mode))
    (packets : List (Packet mode)) (entry : Entry mode)
    (member : List.Mem entry (ControlPacking.place mode (start + size mode leading) packets)) :
    List.Mem entry (place mode start (leading ++ adjacent mode packets ++ trailing)) := by
  rw [place_append, place_append, adjacent_place]
  exact List.mem_append_left _ (List.mem_append_right _ member)

end SmcTuring.Native.SpacedPacking

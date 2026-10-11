module
public import SmcTuring.Native.AlignedTemplates

public section

namespace SmcTuring.Native.AlignedPool

open ControlImage AlignedTemplates

inductive Kind where
  | reader (top slot : Nat)
  | scalar

@[expose] def pieces (mode : Mode) (kind : Kind) (cursor : Nat) (initial : Word mode) : List (SpacedPacking.Piece mode) :=
  match kind with | .reader top slot => readerPieces mode cursor top slot initial | .scalar => scalarPieces mode cursor initial
@[expose] def next (mode : Mode) (kind : Kind) (cursor : Nat) : Nat :=
  match kind with | .reader _ _ => readerEnd mode cursor | .scalar => scalarEnd mode cursor
@[expose] def field (mode : Mode) (kind : Kind) (cursor : Nat) : Word mode :=
  match kind with
  | .reader _ _ => ReaderImage.label mode (AlignedPacking.readerStart mode cursor)
  | .scalar => AlignedPacking.scalarLabel mode cursor
@[expose] def fragment (mode : Mode) (kind : Kind) (cursor : Nat) (initial : Word mode) : List (Entry mode) :=
  match kind with
  | .reader top slot => ControlPacking.place mode (AlignedPacking.readerStart mode cursor)
      (ReadCalleeImage.packets mode (AlignedPacking.readerStart mode cursor) top slot initial)
  | .scalar => ControlPacking.place mode (AlignedPacking.scalarStart mode cursor) [.owned initial]
@[expose] def Fits (mode : Mode) (kind : Kind) (cursor : Nat) : Prop :=
  match kind with
  | .reader _ _ => readerEnd mode cursor < 2 ^ (8 * mode.wordBytes)
  | .scalar => AlignedPacking.scalarStart mode cursor + moffsOperandOffset mode < 2 ^ (8 * mode.wordBytes)

structure Facts (mode : Mode) (kind : Kind) (cursor origin gridBase : Nat) (initial : Word mode)
    (whole : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode) : Prop where
  within : Fragment.Within mode (fragment mode kind cursor initial) (SpacedPacking.place mode origin whole)
  owned : SpacedCombinedImage.Owned mode whole origin gridBase (field mode kind cursor)
  initialized : Execution.load mode (SpacedCombinedImage.image mode whole origin gridBase values) (field mode kind cursor) = initial
  aligned : (field mode kind cursor).toNat % mode.wordBytes = 0

private theorem extent (mode : Mode) (kind : Kind) (cursor : Nat) (initial : Word mode) :
    cursor + SpacedPacking.size mode (pieces mode kind cursor initial) = next mode kind cursor := by
  cases kind with
  | reader top slot => exact reader_extent mode cursor top slot initial
  | scalar => exact scalar_extent mode cursor initial

private theorem template_constructed (mode : Mode) (kind : Kind) (cursor origin gridBase : Nat) (initial : Word mode)
    (leading trailing : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode)
    (location : cursor = origin + SpacedPacking.size mode leading) (fits : Fits mode kind cursor) :
    Facts mode kind cursor origin gridBase initial (leading ++ pieces mode kind cursor initial ++ trailing) values := by
  cases kind with
  | reader top slot =>
    have constructed := reader_constructed mode cursor top slot origin gridBase initial leading trailing values location fits
    exact ⟨constructed.within, constructed.owned, constructed.initialized, constructed.aligned⟩
  | scalar =>
    have constructed := scalar_constructed mode cursor origin gridBase initial leading trailing values location fits
    exact ⟨constructed.within, constructed.owned, constructed.initialized, constructed.aligned⟩

@[expose] def pool (mode : Mode) (kind : Kind) : Nat -> List (Word mode) -> List (SpacedPacking.Piece mode)
  | _, [] => []
  | cursor, initial :: rest => pieces mode kind cursor initial ++ pool mode kind (next mode kind cursor) rest
@[expose] def endPosition (mode : Mode) (kind : Kind) : Nat -> List (Word mode) -> Nat
  | cursor, [] => cursor
  | cursor, _ :: rest => endPosition mode kind (next mode kind cursor) rest
@[expose] def cursorAt (mode : Mode) (kind : Kind) : Nat -> Nat -> Nat
  | cursor, 0 => cursor
  | cursor, index + 1 => cursorAt mode kind (next mode kind cursor) index

/-- The complete finite pool has a computed extent. Its cursor evolution is
independent of operand values and contains no future-execution information. -/
theorem pool_extent (mode : Mode) (kind : Kind) (cursor : Nat) (payloads : List (Word mode)) :
    cursor + SpacedPacking.size mode (pool mode kind cursor payloads) = endPosition mode kind cursor payloads := by
  induction payloads generalizing cursor with
  | nil => simp only [pool, SpacedPacking.size, List.map_nil, List.sum_nil, Nat.add_zero, endPosition]
  | cons initial rest ih =>
    rw [pool, SpacedPacking.size_append, ←Nat.add_assoc, extent, ih]
    rfl

/-- Pool geometry depends only on the number of words, not their values. -/
theorem end_cursor (mode : Mode) (kind : Kind) (cursor : Nat) (payloads : List (Word mode)) :
    endPosition mode kind cursor payloads = cursorAt mode kind cursor payloads.length := by
  induction payloads generalizing cursor with
  | nil => rfl
  | cons initial rest ih => exact ih (next mode kind cursor)

theorem reader_cursor (mode : Mode) (top slot cursor index : Nat) :
    cursorAt mode (.reader top slot) cursor index = cursorAt mode (.reader 0 0) cursor index := by
  induction index generalizing cursor with
  | zero => rfl
  | succ index ih => exact ih (next mode (.reader 0 0) cursor)

/-- Every pool field is an actual initialized, aligned, code-owned operand.
Every complete helper fragment belongs to the constructed whole byte image. -/
theorem pool_constructed (mode : Mode) (kind : Kind) (cursor origin gridBase : Nat) (payloads : List (Word mode))
    (leading trailing : List (SpacedPacking.Piece mode)) (values : Nat -> Word mode)
    (location : cursor = origin + SpacedPacking.size mode leading)
    (fits : forall index, index < payloads.length -> Fits mode kind (cursorAt mode kind cursor index))
    (index : Nat) (inside : index < payloads.length) :
    Facts mode kind (cursorAt mode kind cursor index) origin gridBase payloads[index]
      (leading ++ pool mode kind cursor payloads ++ trailing) values := by
  induction payloads generalizing cursor leading index with
  | nil => simp at inside
  | cons initial rest ih =>
    cases index with
    | zero =>
      have constructed := template_constructed mode kind cursor origin gridBase initial leading
        (pool mode kind (next mode kind cursor) rest ++ trailing) values location (fits 0 (by simp))
      simpa only [pool, cursorAt, List.getElem_cons_zero, List.append_assoc] using constructed
    | succ index =>
      have tailInside : index < rest.length := Nat.lt_of_succ_lt_succ inside
      have tailLocation : next mode kind cursor = origin + SpacedPacking.size mode (leading ++ pieces mode kind cursor initial) := by
        rw [SpacedPacking.size_append, ←extent mode kind cursor initial, location, Nat.add_assoc]
      have later := ih (next mode kind cursor) (leading ++ pieces mode kind cursor initial) tailLocation
        (fun observed bounded => fits (observed + 1) (Nat.succ_lt_succ bounded)) index tailInside
      simpa only [pool, cursorAt, List.getElem_cons_succ, List.append_assoc] using later

end SmcTuring.Native.AlignedPool

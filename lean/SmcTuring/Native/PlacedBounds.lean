module
public import SmcTuring.Native.ReaderBounds
public import SmcTuring.Native.ReadScalarBounds

public section

namespace SmcTuring.Native.PlacedBounds

open Execution MemoryRegion RegionExecution ControlImage

/-- One static control interval, including conservative live-fetch backing bytes.
This depends on placement, not on any later execution. -/
@[expose] def ControlWithin (mode : Mode) (region : Region) (origin : Nat)
    (whole : List (SpacedPacking.Piece mode)) : Prop :=
  region.Contains origin (SpacedPacking.size mode whole + 15)

theorem snippet_bounds (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (origin start : Nat)
    (packets : List (Packet mode)) (nonempty : packets ≠ [])
    (within : Fragment.Within mode (ControlPacking.place mode start packets) (SpacedPacking.place mode origin whole)) :
    origin ≤ start ∧ start + ControlPacking.size mode packets ≤ origin + SpacedPacking.size mode whole := by
  induction packets generalizing start with
  | nil => exact False.elim (nonempty rfl)
  | cons packet rest ih =>
    have firstMember : ({ pc := start, packet := packet } : Entry mode) ∈ ControlPacking.place mode start (packet :: rest) := List.Mem.head _
    have lower := SpacedPacking.placed_lower mode whole origin _ (within _ firstMember)
    refine ⟨lower, ?_⟩
    cases rest with
    | nil =>
      have upper := SpacedPacking.placed_upper mode whole origin _ (within _ firstMember)
      simpa only [ControlPacking.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Entry.bytes] using upper
    | cons next tail =>
      have later : Fragment.Within mode (ControlPacking.place mode (start + (packet.bytes mode).length) (next :: tail))
          (SpacedPacking.place mode origin whole) := by
        intro entry member
        exact within entry (List.Mem.tail _ member)
      have upper := (ih (start + (packet.bytes mode).length) (by intro absent; cases absent) later).2
      simpa only [ControlPacking.size, List.map_cons, List.sum_cons, Nat.add_assoc] using upper

theorem snippet_window (mode : Mode) (region : Region) (origin start : Nat)
    (whole : List (SpacedPacking.Piece mode)) (packets : List (Packet mode))
    (code : ControlWithin mode region origin whole) (nonempty : packets ≠ [])
    (within : Fragment.Within mode (ControlPacking.place mode start packets) (SpacedPacking.place mode origin whole)) :
    region.Contains start (ControlPacking.size mode packets + 15) := by
  have bounds := snippet_bounds mode whole origin start packets nonempty within
  rcases code with ⟨lower, upper⟩
  constructor <;> omega

theorem entry_window (mode : Mode) (region : Region) (origin : Nat)
    (whole : List (SpacedPacking.Piece mode)) (entry : Entry mode)
    (code : ControlWithin mode region origin whole) (member : entry ∈ SpacedPacking.place mode origin whole) :
    region.Contains entry.pc 15 := by
  have boundsLower := SpacedPacking.placed_lower mode whole origin entry member
  have boundsUpper := SpacedPacking.placed_upper mode whole origin entry member
  rcases code with ⟨lower, upper⟩
  constructor <;> omega

theorem scalar_safe (mode : Mode) (region : Region) (op : ScalarImage.Op) (layout : ScalarImage.Layout mode)
    (state : State mode) (ready : ScalarImage.Ready mode op layout state)
    (code : ControlWithin mode region layout.origin layout.whole)
    (target : region.Contains (Arithmetic.encodeNat mode layout.target).toNat mode.wordBytes) :
    SafeRun mode region (ScalarImage.program mode op layout) state :=
  ScalarBounds.safe_run mode region op layout state ready (entry_window mode region _ _ _ code ready.member) target

theorem calls_safe (mode : Mode) (region : Region) (origin start top slot : Nat)
    (whole : List (SpacedPacking.Piece mode)) (transfer : CallsImage.Transfer) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : CallsImage.Ranges mode start top transfer)
    (fits : start + CallsImage.totalSize mode transfer < 2 ^ (8 * mode.wordBytes))
    (value : load mode state.memory (Arithmetic.encodeNat mode top) = Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes)
    (within : Fragment.Within mode (ControlPacking.place mode start (CallsImage.packets mode start top transfer)) (SpacedPacking.place mode origin whole))
    (code : ControlWithin mode region origin whole)
    (topInside : region.Contains (Arithmetic.encodeNat mode top).toNat mode.wordBytes)
    (slotInside : region.Contains (Arithmetic.encodeNat mode slot).toNat mode.wordBytes)
    (targetInside : CallsBounds.TargetWithin mode region transfer) :
    SafeRun mode region (Calls.program mode (CallsImage.firstDisp mode start top) (CallsImage.secondDisp mode start top)
      (CallsImage.callTarget mode start transfer)) state := by
  have span := snippet_window mode region origin start whole _ code (by simp [CallsImage.packets]) within
  rw [CallsImage.packet_size] at span
  exact CallsBounds.safe_run mode region start top slot transfer state location ranges fits value span topInside slotInside targetInside

theorem reader_invocation_safe (mode : Mode) (region : Region) (layout : ReadInvocationImage.Layout mode)
    (state : State mode) (ready : ReadInvocationImage.Ready mode layout state)
    (code : ControlWithin mode region layout.origin layout.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.slot).toNat mode.wordBytes)
    (pointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.callee)).toNat mode.wordBytes) :
    SafeRun mode region (ReadInvocationImage.program mode layout state) state := by
  have caller := snippet_window mode region _ _ _ _ code (by simp [CallsImage.packets]) ready.callerWithin
  rw [CallsImage.packet_size] at caller
  have callee := snippet_window mode region _ _ _ _ code (by simp [ReadCalleeImage.packets, ReaderImage.packets]) ready.calleeWithin
  rw [ReadCalleeImage.packet_size] at callee
  exact ReadInvocationBounds.safe_run mode region layout state ready caller callee top slot pointer

theorem read_scalar_safe (mode : Mode) (region : Region) (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode)
    (state : State mode) (ready : ReadScalarImage.Ready mode op layout state)
    (code : ControlWithin mode region layout.reader.origin layout.reader.whole)
    (top : region.Contains (Arithmetic.encodeNat mode layout.reader.top).toNat mode.wordBytes)
    (slot : region.Contains (Arithmetic.encodeNat mode layout.reader.slot).toNat mode.wordBytes)
    (pointer : region.Contains (load mode state.memory (ReaderImage.label mode layout.reader.callee)).toNat mode.wordBytes)
    (target : region.Contains (Arithmetic.encodeNat mode layout.target).toNat mode.wordBytes) :
    SafeRun mode region (ReadScalarImage.program mode op layout state) state := by
  have first := reader_invocation_safe mode region layout.reader state ready.readReady code top slot pointer
  have second := scalar_safe mode region op (ReadScalarImage.scalarLayout mode layout) (ReadScalarImage.afterRead mode layout state)
    (ReadScalarImage.scalar_ready mode op layout state ready) code target
  apply WindowBounds.safe_run_append mode region _ _ state first
  exact second

/-- Compose independently derived access bounds at a proved execution boundary. -/
theorem safe_trace_append (mode : Mode) (region : Region) {initial middle : State mode}
    {first second : List (Form mode)} (trace : Fetch.Trace mode initial first middle)
    (firstSafe : SafeRun mode region first initial) (secondSafe : SafeRun mode region second middle) :
    SafeRun mode region (first ++ second) initial := by
  apply WindowBounds.safe_run_append mode region first second initial firstSafe
  rw [(Fetch.trace_run_eq mode trace).symm]
  exact secondSafe

end SmcTuring.Native.PlacedBounds

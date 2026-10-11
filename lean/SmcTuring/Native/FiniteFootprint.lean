module
public import SmcTuring.Native.LoadedExecution

public section

namespace SmcTuring.Native.FiniteFootprint

open Execution MemoryRegion RegionExecution

/-- The containing interval for both finite regions. Gaps are ordinary loaded
backing bytes; this operation makes no mapping or canonical-address assertion. -/
@[expose] def join (first second : Region) : Region :=
  ⟨min first.lower second.lower, max first.upper second.upper⟩

@[expose] def Widens (smaller larger : Region) : Prop :=
  larger.lower ≤ smaller.lower ∧ smaller.upper ≤ larger.upper

theorem join_left (first second : Region) : Widens first (join first second) :=
  ⟨Nat.min_le_left _ _, Nat.le_max_left _ _⟩

theorem join_right (first second : Region) : Widens second (join first second) :=
  ⟨Nat.min_le_right _ _, Nat.le_max_right _ _⟩

theorem contains_widen {smaller larger : Region} (wider : Widens smaller larger)
    (address count : Nat) (within : smaller.Contains address count) : larger.Contains address count :=
  ⟨Nat.le_trans wider.1 within.1, Nat.le_trans within.2 wider.2⟩

theorem safe_widen (mode : Mode) {smaller larger : Region} (wider : Widens smaller larger)
    (form : Form mode) (state : State mode) (safe : Safe mode smaller form state) :
    Safe mode larger form state := by
  refine ⟨⟨contains_widen wider _ _ safe.1.1, ?_⟩, ?_, contains_widen wider _ _ safe.2.2⟩
  · cases classified : Fetch.lengthOfBytes mode (ByteMemory.bytesAt state.memory state.pc.toNat 3) with
    | none => trivial
    | some count =>
      exact contains_widen wider _ _ (by simpa only [classified] using safe.1.2)
  · unfold ReadWithin
    cases read : readAddress mode form state with
    | none => trivial
    | some address =>
      exact contains_widen wider _ _ (by simpa only [ReadWithin, read] using safe.2.1)

theorem safe_run_widen (mode : Mode) {smaller larger : Region} (wider : Widens smaller larger)
    (forms : List (Form mode)) (state : State mode) (safe : SafeRun mode smaller forms state) :
    SafeRun mode larger forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    exact ⟨safe_widen mode wider form state safe.1, ih (execute mode form state) safe.2⟩

/-- A computed finite extent for the live header, classifier-selected packet,
data read (if any), and full word write of one event. No extent bound is assumed. -/
@[expose] def event (mode : Mode) (form : Form mode) (state : State mode) : Region :=
  let pc := state.pc.toNat
  let count := (Fetch.lengthOfBytes mode (ByteMemory.bytesAt state.memory pc 3)).getD 0
  let read := ((readAddress mode form state).map BitVec.toNat).getD pc
  let written := (Writes.address mode form state).toNat
  ⟨min pc (min read written), max (pc + 3) (max (pc + count) (max (read + mode.wordBytes) (written + mode.wordBytes)))⟩

theorem event_safe (mode : Mode) (form : Form mode) (state : State mode) :
    Safe mode (event mode form state) form state := by
  cases classified : Fetch.lengthOfBytes mode (ByteMemory.bytesAt state.memory state.pc.toNat 3) <;>
    cases read : readAddress mode form state <;>
    simp only [Safe, FetchWithin, ReadWithin, event, classified, read, Option.getD, Option.map,
      Region.Contains]
  all_goals repeat constructor
  all_goals first | trivial | omega | exact ⟨trivial, by omega⟩

/-- A containing interval for a finite sequence, computed after each prior
write. An empty suffix contributes its final PC as a zero-width interval. -/
@[expose] def run (mode : Mode) : List (Form mode) → State mode → Region
  | [], state => ⟨state.pc.toNat, state.pc.toNat⟩
  | form :: rest, state => join (event mode form state) (run mode rest (execute mode form state))

/-- Every finite selected-form run has a computed finite access bound. -/
theorem run_safe (mode : Mode) (forms : List (Form mode)) (state : State mode) :
    SafeRun mode (run mode forms state) forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    exact ⟨safe_widen mode (join_left _ _) form state (event_safe mode form state),
      safe_run_widen mode (join_right _ _) rest (execute mode form state) (ih (execute mode form state))⟩

/-- Finite loading is constructed for every actual fetched finite prefix.
Neither a safe trace nor a conclusion about finite execution is a premise.
The result does not assert that its natural-address interval is physically mapped. -/
theorem loaded_prefix (mode : Mode) {state finish : State mode} {forms : List (Form mode)}
    (trace : Fetch.Trace mode state forms finish) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode (run mode forms state)
        (LoadedExecution.snapshot mode (run mode forms state) state) forms loadedFinish ∧
      StateAgree mode (run mode forms state)
        (LoadedExecution.expand mode (run mode forms state) loadedFinish) finish :=
  LoadedExecution.trace_complete mode (run mode forms state) trace (run_safe mode forms state)
    _ (LoadedExecution.snapshot_agrees mode _ state)

end SmcTuring.Native.FiniteFootprint

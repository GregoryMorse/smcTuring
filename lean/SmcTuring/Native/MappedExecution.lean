module
public import SmcTuring.Native.AddressSpace
public import SmcTuring.Native.LoadedExecution

public section

namespace SmcTuring.Native.MappedExecution

open MemoryRegion RegionExecution

inductive Access where
  | read | write | execute
  deriving DecidableEq, Repr

/-- Effective linear-address permissions for one stable mapping. Relating these
bits to actual page tables, segmentation and processor configuration is external. -/
structure Environment where
  paging : AddressSpace.Paging
  readable : Nat → Bool
  writable : Nat → Bool
  executable : Nat → Bool

@[expose] def permission (environment : Environment) : Access → Nat → Bool
  | .read => environment.readable
  | .write => environment.writable
  | .execute => environment.executable

@[expose] def Window (mode : Mode) (environment : Environment) (access : Access) (address count : Nat) : Prop :=
  ∀ index : Fin count, AddressSpace.Valid mode environment.paging (address + index.val) ∧
    permission environment access (address + index.val) = true

instance (mode : Mode) (environment : Environment) (access : Access) (address count : Nat) :
    Decidable (Window mode environment access address count) := by
  unfold Window
  infer_instance

/-- Static allocation certificate, containing no future trace or runtime state. -/
structure Mapped (mode : Mode) (environment : Environment) (region : Region) : Prop where
  fits : AddressSpace.Fits mode environment.paging region
  read : ∀ address, region.lower ≤ address → address < region.upper → environment.readable address = true
  write : ∀ address, region.lower ≤ address → address < region.upper → environment.writable address = true
  execute : ∀ address, region.lower ≤ address → address < region.upper → environment.executable address = true

theorem window_of_contains (mode : Mode) (environment : Environment) (region : Region)
    (mapped : Mapped mode environment region) (access : Access) (address count : Nat)
    (contained : region.Contains address count) : Window mode environment access address count := by
  intro index
  have byte := contains_byte region address count contained index
  refine ⟨AddressSpace.contains_valid mode environment.paging region mapped.fits address count contained index, ?_⟩
  cases access with
  | read => exact mapped.read _ byte.1 byte.2
  | write => exact mapped.write _ byte.1 byte.2
  | execute => exact mapped.execute _ byte.1 byte.2

/-- Live classifier header/full packet, selected data read and complete write,
including CALL's actual decremented-SP destination. -/
@[expose] def Accesses (mode : Mode) (environment : Environment) (form : Form mode) (state : Execution.State mode) : Prop :=
  (Window mode environment .execute state.pc.toNat 3 ∧
    match Fetch.lengthOfBytes mode (ByteMemory.bytesAt state.memory state.pc.toNat 3) with
    | none => True
    | some count => Window mode environment .execute state.pc.toNat count) ∧
  (match readAddress mode form state with
    | none => True
    | some address => Window mode environment .read address.toNat mode.wordBytes) ∧
  Window mode environment .write (Writes.address mode form state).toNat mode.wordBytes

instance (mode : Mode) (environment : Environment) (form : Form mode) (state : Execution.State mode) :
    Decidable (Accesses mode environment form state) := by
  unfold Accesses
  cases Fetch.lengthOfBytes mode (ByteMemory.bytesAt state.memory state.pc.toNat 3) <;>
    cases readAddress mode form state <;> infer_instance

theorem accesses_of_safe (mode : Mode) (environment : Environment) (region : Region)
    (mapped : Mapped mode environment region) (form : Form mode) (state : Execution.State mode)
    (safe : Safe mode region form state) : Accesses mode environment form state := by
  refine ⟨⟨window_of_contains mode environment region mapped .execute _ _ safe.1.1, ?_⟩, ?_,
    window_of_contains mode environment region mapped .write _ _ safe.2.2⟩
  · cases length : Fetch.lengthOfBytes mode (ByteMemory.bytesAt state.memory state.pc.toNat 3) with
    | none => trivial
    | some count =>
      exact window_of_contains mode environment region mapped .execute _ _ (by simpa only [length] using safe.1.2)
  · cases read : readAddress mode form state with
    | none => trivial
    | some address =>
      exact window_of_contains mode environment region mapped .read _ _ (by simpa only [ReadWithin, read] using safe.2.1)

/-- Live-byte finite execution with explicit address/permission rejection.
The returned form is an event and is never an input to this evaluator. -/
@[expose] def step (mode : Mode) (environment : Environment) (region : Region)
    (state : LoadedExecution.State mode region) : Option (Form mode × LoadedExecution.State mode region) :=
  (LoadedExecution.step mode region state).bind fun result =>
    if Accesses mode environment result.1 (LoadedExecution.expand mode region state) then some result else none

theorem step_complete (mode : Mode) (environment : Environment) (region : Region)
    (mapped : Mapped mode environment region) (state finish : LoadedExecution.State mode region) (form : Form mode)
    (stepped : LoadedExecution.step mode region state = some (form, finish)) :
    step mode environment region state = some (form, finish) := by
  have safe := (LoadedExecution.step_sound mode region state finish (LoadedExecution.expand mode region state) form
    (state_agree_refl mode region _) stepped).2.1
  have allowed := accesses_of_safe mode environment region mapped form _ safe
  simp only [step, stepped, Option.bind_some, ite_eq_left allowed]

theorem step_sound (mode : Mode) (environment : Environment) (region : Region)
    (state finish : LoadedExecution.State mode region) (form : Form mode)
    (stepped : step mode environment region state = some (form, finish)) :
    LoadedExecution.step mode region state = some (form, finish) ∧
      Accesses mode environment form (LoadedExecution.expand mode region state) := by
  unfold step at stepped
  cases selected : LoadedExecution.step mode region state with
  | none => simp only [selected, Option.bind_none, reduceCtorEq] at stepped
  | some result =>
    simp only [selected, Option.bind_some] at stepped
    split at stepped
    next allowed =>
      have paired := Option.some.inj stepped
      subst result
      exact ⟨rfl, allowed⟩
    next denied => simp only [reduceCtorEq] at stepped

/-- Missing execute permission is rejected, irrespective of decoder success. -/
theorem step_execute_denied (mode : Mode) (environment : Environment) (region : Region)
    (state : LoadedExecution.State mode region) (denied : environment.executable state.pc.toNat = false) :
    step mode environment region state = none := by
  have disallowed : ∀ form, ¬ Accesses mode environment form (LoadedExecution.expand mode region state) := by
    intro form allowed
    have first := (allowed.1.1 (⟨0, by decide⟩ : Fin 3)).2
    change environment.executable (state.pc.toNat + 0) = true at first
    simp only [Nat.add_zero, denied, Bool.false_eq_true] at first
  cases selected : LoadedExecution.step mode region state with
  | none => simp only [step, selected, Option.bind_none]
  | some result => simp only [step, selected, Option.bind_some, ite_eq_right (disallowed result.1)]

/-- A noncanonical PC is an evaluator rejection, not an intended source halt. -/
theorem step_invalid_pc (mode : Mode) (environment : Environment) (region : Region)
    (state : LoadedExecution.State mode region) (invalid : ¬ AddressSpace.Valid mode environment.paging state.pc.toNat) :
    step mode environment region state = none := by
  have disallowed : ∀ form, ¬ Accesses mode environment form (LoadedExecution.expand mode region state) := by
    intro form allowed
    have first := (allowed.1.1 (⟨0, by decide⟩ : Fin 3)).1
    change AddressSpace.Valid mode environment.paging (state.pc.toNat + 0) at first
    exact invalid (by simpa only [Nat.add_zero] using first)
  cases selected : LoadedExecution.step mode region state with
  | none => simp only [step, selected, Option.bind_none]
  | some result => simp only [step, selected, Option.bind_some, ite_eq_right (disallowed result.1)]

inductive Trace (mode : Mode) (environment : Environment) (region : Region) :
    LoadedExecution.State mode region → List (Form mode) → LoadedExecution.State mode region → Prop where
  | nil (state) : Trace mode environment region state [] state
  | step {state finish next} {form} {rest}
      (stepped : step mode environment region state = some (form, next))
      (tail : Trace mode environment region next rest finish) : Trace mode environment region state (form :: rest) finish

theorem trace_complete (mode : Mode) (environment : Environment) (region : Region)
    (mapped : Mapped mode environment region) {state finish : LoadedExecution.State mode region}
    {forms : List (Form mode)} (trace : LoadedExecution.Trace mode region state forms finish) :
    Trace mode environment region state forms finish := by
  induction trace with
  | nil => exact Trace.nil _
  | step stepped _ ih => exact Trace.step (step_complete mode environment region mapped _ _ _ stepped) ih

@[expose] def AccessRun (mode : Mode) (environment : Environment) : List (Form mode) → Execution.State mode → Prop
  | [], _ => True
  | form :: rest, state => Accesses mode environment form state ∧
      AccessRun mode environment rest (Execution.execute mode form state)

theorem access_run_of_safe (mode : Mode) (environment : Environment) (region : Region)
    (mapped : Mapped mode environment region) (forms : List (Form mode)) (state : Execution.State mode)
    (safe : SafeRun mode region forms state) : AccessRun mode environment forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih => exact ⟨accesses_of_safe mode environment region mapped form state safe.1, ih _ safe.2⟩

theorem trace_loaded (mode : Mode) (environment : Environment) (region : Region)
    {state finish : LoadedExecution.State mode region} {forms : List (Form mode)}
    (trace : Trace mode environment region state forms finish) : LoadedExecution.Trace mode region state forms finish := by
  induction trace with
  | nil => exact LoadedExecution.Trace.nil _
  | step stepped _ ih => exact LoadedExecution.Trace.step (step_sound mode environment region _ _ _ stepped).1 ih

/-- Refines automatic fetch and proves all modeled checks at each actual state.
Physical instruction-fetch coherence remains an explicit external contract. -/
theorem trace_sound (mode : Mode) (environment : Environment) (region : Region)
    (mapped : Mapped mode environment region) {state finish : LoadedExecution.State mode region}
    {forms : List (Form mode)} (trace : Trace mode environment region state forms finish)
    (model : Execution.State mode) (same : StateAgree mode region (LoadedExecution.expand mode region state) model) :
    Fetch.Trace mode model forms (Execution.runForms mode forms model) ∧
      AccessRun mode environment forms model ∧
      StateAgree mode region (LoadedExecution.expand mode region finish) (Execution.runForms mode forms model) := by
  have original := LoadedExecution.trace_sound mode region (trace_loaded mode environment region trace) model same
  exact ⟨original.1, access_run_of_safe mode environment region mapped forms model original.2.1, original.2.2⟩

end SmcTuring.Native.MappedExecution

module
public import SmcTuring.Native.MappedExecution

public section

namespace SmcTuring.Native.ControlBounds

open Execution MemoryRegion RegionExecution MappedExecution

/-- Near CALL validates its actual target before loading the instruction pointer.
The target is evaluated by the selected effect, including pre-push indirect read. -/
@[expose] def TargetValid (mode : Mode) (environment : Environment) (form : Form mode) (state : Execution.State mode) : Prop :=
  match form with
  | .callRelative _ | .memory .callIndirect _ => AddressSpace.Valid mode environment.paging (Execution.execute mode form state).pc.toNat
  | _ => True

@[expose] def Targets (mode : Mode) (environment : Environment) : List (Form mode) → Execution.State mode → Prop
  | [], _ => True
  | form :: rest, state => TargetValid mode environment form state ∧ Targets mode environment rest (Execution.execute mode form state)

theorem pc_valid_of_safe (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) (forms : List (Form mode)) (state : Execution.State mode)
    (nonempty : forms ≠ []) (safe : SafeRun mode region forms state) :
    AddressSpace.Valid mode environment.paging state.pc.toNat := by
  cases forms with
  | nil => exact False.elim (nonempty rfl)
  | cons form rest =>
    have first := AddressSpace.contains_valid mode environment.paging region mapping.fits state.pc.toNat 3 safe.1.1.1
      (⟨0, by decide⟩ : Fin 3)
    simpa only [Nat.add_zero] using first

/-- Every interior target is the PC of the next actual contained instruction.
The final target requires its own validity premise because no next fetch occurs. -/
theorem targets_of_safe (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) (forms : List (Form mode)) (state : Execution.State mode)
    (safe : SafeRun mode region forms state)
    (ending : AddressSpace.Valid mode environment.paging (Execution.runForms mode forms state).pc.toNat) :
    Targets mode environment forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    have nextValid : AddressSpace.Valid mode environment.paging (Execution.execute mode form state).pc.toNat := by
      cases rest with
      | nil => simpa only [Execution.runForms] using ending
      | cons next tail => exact pc_valid_of_safe mode environment region mapping _ _ (by simp) safe.2
    refine ⟨?_, ih _ safe.2 ending⟩
    cases form with
    | moffs address => trivial
    | exchangeIndirect => trivial
    | callRelative displacement => exact nextValid
    | memory operation displacement => cases operation <;> first | exact nextValid | trivial

theorem targets_of_trace (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) {state finish : Execution.State mode} {forms : List (Form mode)}
    (trace : Fetch.Trace mode state forms finish) (safe : SafeRun mode region forms state)
    (ending : AddressSpace.Valid mode environment.paging finish.pc.toNat) : Targets mode environment forms state :=
  targets_of_safe mode environment region mapping forms state safe (by rw [←Fetch.trace_run_eq mode trace]; exact ending)

end SmcTuring.Native.ControlBounds

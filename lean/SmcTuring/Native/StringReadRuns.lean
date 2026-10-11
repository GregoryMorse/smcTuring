module
public import SmcTuring.Native.StringReadAgreement
public import SmcTuring.Native.StringTraceChecks

public section
namespace SmcTuring.Native.StringReadRuns
open StringReadWindows StringReadAgreement MemoryRegion

/-- Data-read containment at the actual successive states, after every
preceding self-modifying store. -/
@[expose] def Run (mode : Mode) (region : Region) : List (StringStack.Form mode) → StringExecution.State mode → Prop
  | [],_ => True
  | form::rest,state => Within mode region form state ∧ Run mode region rest (StringStack.execute mode form state)

theorem append (mode : Mode) (region : Region) (first second : List (StringStack.Form mode))
    (state : StringExecution.State mode) :
    Run mode region (first++second) state ↔ Run mode region first state ∧ Run mode region second (StringWrites.run mode first state) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append,Run,StringWrites.run,true_and]
  | cons form rest ih => simp only [List.cons_append,Run,StringWrites.run,ih,and_assoc]

/-- Static scalar-form classification plus the original complete store
certificate derives every later data-read bound; no later state is supplied. -/
theorem local_of_owned (mode : Mode) (start stop : Nat) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode) (localReads : ∀ form∈forms,Local mode form)
    (owned : StringWrites.OwnedRun mode start stop forms state) : Run mode ⟨start,stop⟩ forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    exact ⟨within_of_owned mode start stop form state (localReads form (List.Mem.head _)) owned.1,
      ih _ (fun later member => localReads later (List.Mem.tail _ member)) owned.2⟩

theorem append_trace (mode : Mode) (region : Region) (first second : List (StringStack.Form mode))
    (state middle : StringExecution.State mode) (actual : StringStack.Trace mode state first middle)
    (leading : Run mode region first state) (trailing : Run mode region second middle) :
    Run mode region (first++second) state := by
  apply (append mode region first second state).mpr
  rw [StringWrites.trace_run_eq mode actual]
  exact ⟨leading,trailing⟩

theorem mono (mode : Mode) (small large : Region) (lower : large.lower≤small.lower) (upper : small.upper≤large.upper)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (contained : Run mode small forms state) : Run mode large forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    refine ⟨?_,ih _ contained.2⟩
    unfold Within Contained
    cases window : read mode form state with
    | none => trivial
    | some packet =>
      have bounds : small.Contains packet.address packet.count := by
        simpa only [Within,Contained,window] using contained.1
      exact ⟨Nat.le_trans lower bounds.1,Nat.le_trans bounds.2 upper⟩

/-- Complete selected effects and the loaded byte image are independent of
exterior memory across the entire actual sequence of declared reads. -/
theorem effects_agree (mode : Mode) (region : Region) (forms : List (StringStack.Form mode))
    (left right : StringExecution.State mode) (same : AgreeState mode region left right)
    (contained : Run mode region forms right) :
    AgreeState mode region (StringWrites.run mode forms left) (StringWrites.run mode forms right) := by
  induction forms generalizing left right with
  | nil => exact same
  | cons form rest ih => exact ih _ _ (execute_agrees mode region form left right same contained.1) contained.2

/-- Any next event is inspected at the reached prefix state of the same
actual current-byte trace, with the original data-read proof split there. -/
theorem next_read (mode : Mode) (region : Region) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (contained : Run mode region forms state) (before : List (StringStack.Form mode))
    (form : StringStack.Form mode) (after : List (StringStack.Form mode)) (cut : before++form::after=forms) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      Within mode region form reached ∧ StringStack.Trace mode (StringStack.execute mode form reached) after finish := by
  rw [←cut] at actual contained
  obtain ⟨reached,leading,trailing⟩:=StringTraceChecks.split_trace mode before (form::after) actual
  have bounds:=(append mode region before (form::after) state).mp contained
  rw [StringWrites.trace_run_eq mode leading] at bounds
  cases trailing with
  | step current tail => exact ⟨reached,leading,current,bounds.2.1,tail⟩

end SmcTuring.Native.StringReadRuns

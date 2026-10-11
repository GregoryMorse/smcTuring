module
public import SmcTuring.Native.StringWrites
public import SmcTuring.Native.MappedExecution

public section
namespace SmcTuring.Native.StringTraceChecks
open StringStack StringWrites MemoryRegion MappedExecution

/-- Split the same actual current-byte trace; no second initialization occurs. -/
theorem split_trace (mode : Mode) {state finish : StringExecution.State mode}
    (first second : List (StringStack.Form mode)) (actual : StringStack.Trace mode state (first++second) finish) :
    ∃ middle, StringStack.Trace mode state first middle ∧ StringStack.Trace mode middle second finish := by
  induction first generalizing state with
  | nil => exact ⟨state,StringStack.Trace.nil _,actual⟩
  | cons form rest ih =>
    cases actual with
    | step current tail =>
      obtain ⟨middle,leading,trailing⟩:=ih tail
      exact ⟨middle,StringStack.Trace.step current leading,trailing⟩

/-- Every prefix ends at its actual reached state, with the original complete
store certificate split at exactly that state. -/
theorem split_owned (mode : Mode) (start stop : Nat) {state finish : StringExecution.State mode}
    (first second : List (StringStack.Form mode)) (actual : StringStack.Trace mode state (first++second) finish)
    (owned : OwnedRun mode start stop (first++second) state) :
    ∃ middle, StringStack.Trace mode state first middle ∧ StringStack.Trace mode middle second finish ∧
      OwnedRun mode start stop first state ∧ OwnedRun mode start stop second middle := by
  obtain ⟨middle,leading,trailing⟩:=split_trace mode first second actual
  have stores:=(owned_run_append mode start stop first second state).mp owned
  rw [trace_run_eq mode leading] at stores
  exact ⟨middle,leading,trailing,stores⟩

/-- Inspect any next instruction in the actual run. Its decoder reads the
memory reached after the prefix, and its nonempty store is fully contained. -/
theorem next_store (mode : Mode) (start stop : Nat) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (owned : OwnedRun mode start stop forms state)
    (before : List (StringStack.Form mode)) (form : StringStack.Form mode) (after : List (StringStack.Form mode))
    (cut : before++form::after=forms) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      CodeWrite mode start stop form reached ∧
      StringStack.Trace mode (execute mode form reached) after finish := by
  rw [←cut] at actual owned
  obtain ⟨reached,leading,trailing,_,stores⟩:=split_owned mode start stop before (form::after) actual owned
  cases trailing with
  | step current tail => exact ⟨reached,leading,current,stores.1,tail⟩

/-- Static effective mapping permissions and canonical interval endpoints
certify every byte of every complete store in the same actual trace.
This does not assert instruction-cache coherence or a physical page table. -/
theorem next_mapped_store (mode : Mode) (environment : Environment) (start stop : Nat)
    (mapping : Mapped mode environment ⟨start,stop⟩) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (owned : OwnedRun mode start stop forms state)
    (before : List (StringStack.Form mode)) (form : StringStack.Form mode) (after : List (StringStack.Form mode))
    (cut : before++form::after=forms) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      CodeWrite mode start stop form reached ∧
      Window mode environment .write (packet mode form reached).address (packet mode form reached).bytes.length ∧
      StringStack.Trace mode (execute mode form reached) after finish := by
  obtain ⟨reached,leading,current,store,tail⟩:=next_store mode start stop actual owned before form after cut
  exact ⟨reached,leading,current,store,
    window_of_contains mode environment ⟨start,stop⟩ mapping .write _ _ ⟨store.2.1,store.2.2⟩,tail⟩

end SmcTuring.Native.StringTraceChecks

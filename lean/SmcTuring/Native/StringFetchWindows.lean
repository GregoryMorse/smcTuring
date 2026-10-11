module
public import SmcTuring.Native.StringRequestBounds
public import SmcTuring.Native.StringPCWindows

public section
namespace SmcTuring.Native.StringFetchWindows
open MemoryRegion

/-- Every actual classifier and packet request, including failed fallbacks,
is contained at the current PC. -/
@[expose] def Within (mode : Mode) (region : Region) (state : StringExecution.State mode) : Prop :=
  ∀ count∈StringFetchRequests.requests mode state.principal.memory state.principal.pc.toNat,
    region.Contains state.principal.pc.toNat count
@[expose] def Run (mode : Mode) (region : Region) : List (StringStack.Form mode)→StringExecution.State mode→Prop
  | [],_ => True
  | form::rest,state => Within mode region state ∧ Run mode region rest (StringStack.execute mode form state)

theorem lift_string_trace (mode : Mode) {state finish : StringExecution.State mode}
    {forms : List (StringForm.Form mode)} (actual : StringExecution.Trace mode state forms finish) :
    StringStack.Trace mode state (forms.map (StringWrites.liftString mode)) finish := by
  have lifted:=StringStack.previous_trace mode (StringControl.previous_trace mode (StringDword.string_trace mode actual))
  unfold StringWrites.liftString
  simpa only [List.map_map,Function.comp_def] using lifted

theorem of_envelope (mode : Mode) (region : Region) (state : StringExecution.State mode) (form : StringStack.Form mode)
    (current : StringStack.fetch mode state.principal.memory state.principal.pc.toNat=some form)
    (envelope : StringPCWindows.Envelope mode region form state) : Within mode region state := by
  intro count requested
  have bound:=StringRequestBounds.fetched mode state.principal.memory state.principal.pc.toNat form current count requested
  exact ⟨envelope.1,by have upper:=envelope.2;omega⟩

/-- The actual trace supplies successful current decoding. Static PC envelopes
then contain every actual request, without a future packet/window premise. -/
theorem of_pc_run (mode : Mode) (region : Region) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (envelopes : StringPCWindows.Run mode region forms state) : Run mode region forms state := by
  induction actual with
  | nil => trivial
  | step current rest ih => exact ⟨of_envelope mode region _ _ current envelopes.1,ih envelopes.2⟩

theorem append (mode : Mode) (region : Region) (first second : List (StringStack.Form mode))
    (state : StringExecution.State mode) :
    Run mode region (first++second) state ↔ Run mode region first state ∧ Run mode region second (StringWrites.run mode first state) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append,Run,StringWrites.run,true_and]
  | cons form rest ih => simp only [List.cons_append,Run,StringWrites.run,ih,and_assoc]

theorem append_trace (mode : Mode) (region : Region) (first second : List (StringStack.Form mode))
    (state middle : StringExecution.State mode) (actual : StringStack.Trace mode state first middle)
    (leading : Run mode region first state) (trailing : Run mode region second middle) : Run mode region (first++second) state := by
  rw [append,StringWrites.trace_run_eq mode actual]
  exact ⟨leading,trailing⟩

theorem next_request (mode : Mode) (region : Region) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (windows : Run mode region forms state) (before : List (StringStack.Form mode))
    (form : StringStack.Form mode) (after : List (StringStack.Form mode)) (cut : before++form::after=forms) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      Within mode region reached ∧ StringStack.Trace mode (StringStack.execute mode form reached) after finish := by
  rw [←cut] at actual windows
  obtain ⟨reached,leading,trailing⟩:=StringTraceChecks.split_trace mode before (form::after) actual
  have bounds:=(append mode region before (form::after) state).mp windows
  rw [StringWrites.trace_run_eq mode leading] at bounds
  cases trailing with
  | step current tail => exact ⟨reached,leading,current,bounds.2.1,tail⟩

end SmcTuring.Native.StringFetchWindows

module
public import SmcTuring.Native.StringStackTraceDeterminism

public section
namespace SmcTuring.Native.StringTemplateTraceSegments
attribute [local irreducible] StringTemplateStates.Run

/-- A positively constructed earlier phase is a segment of the same actual
full trace. No equality of independently chosen future states is assumed. -/
theorem segment (mode : Mode) (property : StringExecution.State mode → Prop)
    (before phase whole : List (StringStack.Form mode))
    (state middle phaseEnd finish : StringExecution.State mode)
    (size : (before++phase).length≤whole.length)
    (leading : StringStack.Trace mode state before middle)
    (short : StringStack.Trace mode state (before++phase) phaseEnd)
    (actual : StringStack.Trace mode state whole finish)
    (kept : StringTemplateStates.Run mode property whole state) :
    StringTemplateStates.Run mode property phase middle := by
  obtain ⟨after,cut,_⟩:=StringStackTraceDeterminism.initial_segment mode (before++phase) whole
    state phaseEnd finish size short actual
  rw [cut,List.append_assoc,StringTemplateStates.append,StringWrites.trace_run_eq mode leading] at kept
  exact ((StringTemplateStates.append mode property phase after middle).mp kept.2).1

/-- Join local executable/owner validity to the global certificate at exactly
the same phase forms and reached state, after deterministic segment binding. -/
theorem join_segment (mode : Mode) (global localProperty : StringExecution.State mode → Prop)
    (before phase whole : List (StringStack.Form mode))
    (state middle phaseEnd finish : StringExecution.State mode)
    (size : (before++phase).length≤whole.length)
    (leading : StringStack.Trace mode state before middle)
    (short : StringStack.Trace mode state (before++phase) phaseEnd)
    (actual : StringStack.Trace mode state whole finish)
    (kept : StringTemplateStates.Run mode global whole state)
    (localKept : StringTemplateStates.Run mode localProperty phase middle) :
    StringTemplateStates.Run mode (fun reached => global reached ∧ localProperty reached) phase middle :=
  JointTemplateStates.join mode global localProperty phase middle
    (segment mode global before phase whole state middle phaseEnd finish size leading short actual kept) localKept

end SmcTuring.Native.StringTemplateTraceSegments

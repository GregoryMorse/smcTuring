module
public import SmcTuring.Native.JointTemplateStates

public section
namespace SmcTuring.Native.StringStackTraceDeterminism

/-- Two actual fetch/execute traces from one state have the same initial
forms. The shorter trace determines the exact reached continuation state. -/
theorem initial_segment (mode : Mode) (short long : List (StringStack.Form mode))
    (state middle finish : StringExecution.State mode) (size : short.length≤long.length)
    (before : StringStack.Trace mode state short middle)
    (whole : StringStack.Trace mode state long finish) :
    ∃ tail, long=short++tail ∧ StringStack.Trace mode middle tail finish := by
  induction short generalizing state middle long finish with
  | nil => cases before;exact ⟨long,rfl,whole⟩
  | cons form rest ih =>
    cases before with
    | step first prior =>
      cases long with
      | nil => simp only [List.length_cons,List.length_nil] at size;omega
      | cons other later =>
        cases whole with
        | step second following =>
          have same : form=other := Option.some.inj (first.symm.trans second)
          subst other
          have smaller : rest.length≤later.length := by
            simpa only [List.length_cons,Nat.succ_le_succ_iff] using size
          obtain ⟨tail,cut,after⟩:=ih _ _ _ _ smaller prior following
          exact ⟨tail,by rw [cut];rfl,after⟩

/-- Equal native instruction counts identify both the entire form list and
its final state. No program or later-state equality is supplied. -/
theorem equal_length (mode : Mode) (first second : List (StringStack.Form mode))
    (state firstEnd secondEnd : StringExecution.State mode) (size : first.length=second.length)
    (a : StringStack.Trace mode state first firstEnd)
    (b : StringStack.Trace mode state second secondEnd) : first=second ∧ firstEnd=secondEnd := by
  obtain ⟨tail,cut,after⟩:=initial_segment mode first second state firstEnd secondEnd (Nat.le_of_eq size) a b
  have empty : tail=[] := by
    have lengths:=congrArg List.length cut
    rw [List.length_append,←size] at lengths
    cases tail with
    | nil => rfl
    | cons => simp only [List.length_cons] at lengths;omega
  subst tail
  rw [List.append_nil] at cut
  cases after
  exact ⟨cut.symm,rfl⟩

/-- Transport every reached-state certificate to an independently built
actual trace of the same length from the same initial state. -/
theorem transport (mode : Mode) (property : StringExecution.State mode → Prop)
    (first second : List (StringStack.Form mode)) (state firstEnd secondEnd : StringExecution.State mode)
    (size : first.length=second.length) (a : StringStack.Trace mode state first firstEnd)
    (b : StringStack.Trace mode state second secondEnd)
    (kept : StringTemplateStates.Run mode property first state) :
    StringTemplateStates.Run mode property second state :=
  (equal_length mode first second state firstEnd secondEnd size a b).1 ▸ kept

end SmcTuring.Native.StringStackTraceDeterminism

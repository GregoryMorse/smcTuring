module
public import SmcTuring.Native.StringTemplateStates

public section
namespace SmcTuring.Native.StringTracePrefixes

theorem tail (mode : Mode) (first second : List (StringStack.Form mode))
    (state middle finalState : StringExecution.State mode)
    (whole : StringStack.Trace mode state (first++second) finalState)
    (before : StringStack.Trace mode state first middle) : StringStack.Trace mode middle second finalState := by
  induction first generalizing state with
  | nil => cases before;exact whole
  | cons form rest ih =>
    cases before with
    | step fetched prior =>
      cases whole with
      | step current later => exact ih _ later prior

end SmcTuring.Native.StringTracePrefixes

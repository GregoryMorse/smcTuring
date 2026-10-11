module
public import SmcTuring.Native.StringPCWindows

public section
namespace SmcTuring.Native.StringPCGuards

theorem append (mode : Mode) (first second : List (StringStack.Form mode))
    (leading : StringPCWindows.Guard mode first) (trailing : StringPCWindows.Guard mode second) :
    StringPCWindows.Guard mode (first++second) := by
  induction first with
  | nil => exact trailing
  | cons form rest ih =>
    simp only [List.cons_append,StringPCWindows.Guard,StringPCSteps.total_append]
    exact ⟨by have enough:=leading.1;omega,ih leading.2⟩

end SmcTuring.Native.StringPCGuards

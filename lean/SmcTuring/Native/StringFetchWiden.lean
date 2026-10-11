module
public import SmcTuring.Native.StringFetchWindows

public section
namespace SmcTuring.Native.StringFetchWiden
open MemoryRegion

theorem within (mode : Mode) (small large : Region) (state : StringExecution.State mode)
    (lower : large.lower≤small.lower) (upper : small.upper≤large.upper)
    (contained : StringFetchWindows.Within mode small state) : StringFetchWindows.Within mode large state := by
  intro count requested
  have bounds:=contained count requested
  exact ⟨Nat.le_trans lower bounds.1,Nat.le_trans bounds.2 upper⟩

theorem run (mode : Mode) (small large : Region) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode) (lower : large.lower≤small.lower) (upper : small.upper≤large.upper)
    (contained : StringFetchWindows.Run mode small forms state) : StringFetchWindows.Run mode large forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih => exact ⟨within mode small large state lower upper contained.1,ih _ contained.2⟩

end SmcTuring.Native.StringFetchWiden

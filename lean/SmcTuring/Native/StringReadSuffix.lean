module
public import SmcTuring.Native.StringReadRuns

public section
namespace SmcTuring.Native.StringReadSuffix
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

/-- Read bounds for a known prefix and scalar classification of its suffix
compose using the actual whole execution's already-derived store bounds. -/
theorem contained (mode : Mode) (start stop : Nat) (first tail : List (StringStack.Form mode))
    (state : StringExecution.State mode)
    (reads : StringReadRuns.Run mode ⟨start,stop⟩ first state)
    (scalar : ∀ form∈tail,StringReadWindows.Local mode form)
    (owned : StringWrites.OwnedRun mode start stop (first++tail) state) :
    StringReadRuns.Run mode ⟨start,stop⟩ (first++tail) state := by
  rw [StringWrites.owned_run_append] at owned
  rw [StringReadRuns.append]
  exact ⟨reads,StringReadRuns.local_of_owned mode start stop tail (StringWrites.run mode first state) scalar owned.2⟩

end SmcTuring.Native.StringReadSuffix

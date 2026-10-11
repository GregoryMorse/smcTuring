module
public import SmcTuring.Native.StringSequenceWrites

public section
namespace SmcTuring.Native.StringDwordRuns

theorem run (mode : Mode) (layouts : List DwordLayout.Layout) (state : StringExecution.State mode) :
    StringWrites.run mode ((StringDwordSequence.program mode layouts).map (StringStoreWrites.liftDword mode)) state=
      StringDwordSequence.finish mode layouts state := by
  induction layouts generalizing state with
  | nil => rfl
  | cons layout layouts ih =>
    rw [StringDwordSequence.program,List.flatMap_cons,List.map_append,StringWrites.run_append,StringSequenceWrites.dword_run]
    exact ih (StringDwordCopy.dwordFinish mode layout state)

end SmcTuring.Native.StringDwordRuns

module
public import SmcTuring.Appendix.Listing8AccumulatorExit
public import SmcTuring.Native.StringReadRuns

public section
namespace SmcTuring.Native.AccumulatorReadClasses

theorem prologue (mode : Mode) (region : MemoryRegion.Region) (a : AccumulatorLayout.Layout)
    (state : StringExecution.State mode) :
    StringReadRuns.Run mode region [StringStack.native mode (AccumulatorLayout.saveForm mode a)] state := by
  simp only [StringReadRuns.Run,and_true]
  cases mode <;> trivial

theorem epilogue (mode : Mode) (a : AccumulatorLayout.Layout) :
    ∀ form∈Appendix.Listing8AccumulatorExit.program mode a,StringReadWindows.Local mode form := by
  cases mode <;> simp [Appendix.Listing8AccumulatorExit.program,AccumulatorLayout.program,
    AccumulatorLayout.first,AccumulatorLayout.second,AccumulatorLayout.third,Reader.storeForm,
    StringStack.native,StringDwordCopy.native,StringReadWindows.Local,StringReadWindows.ControlLocal,
    StringReadWindows.DwordLocal,StringReadWindows.StringLocal,StringReadWindows.NativeLocal]

end SmcTuring.Native.AccumulatorReadClasses

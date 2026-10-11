module
public import SmcTuring.Native.StringWrites

public section
namespace SmcTuring.Native.StringWriteRegions

theorem code_mono (mode : Mode) (smallStart smallEnd largeStart largeEnd : Nat)
    (lower : largeStart≤smallStart) (upper : smallEnd≤largeEnd)
    (form : StringStack.Form mode) (state : StringExecution.State mode)
    (owned : StringWrites.CodeWrite mode smallStart smallEnd form state) :
    StringWrites.CodeWrite mode largeStart largeEnd form state :=
  ⟨owned.1,Nat.le_trans lower owned.2.1,Nat.le_trans owned.2.2 upper⟩

/-- Widen only the static containing code interval; every actual packet,
instruction and state in the architectural execution stays the same. -/
theorem owned_mono (mode : Mode) (smallStart smallEnd largeStart largeEnd : Nat)
    (lower : largeStart≤smallStart) (upper : smallEnd≤largeEnd)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (owned : StringWrites.OwnedRun mode smallStart smallEnd forms state) :
    StringWrites.OwnedRun mode largeStart largeEnd forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    exact ⟨code_mono mode smallStart smallEnd largeStart largeEnd lower upper form state owned.1,
      ih _ owned.2⟩

/-- Every exterior byte window is retained on the same actual owned trace. -/
theorem trace_window (mode : Mode) (codeStart codeEnd : Nat)
    {forms : List (StringStack.Form mode)} {initial finalState : StringExecution.State mode}
    (actual : StringStack.Trace mode initial forms finalState)
    (owned : StringWrites.OwnedRun mode codeStart codeEnd forms initial)
    (observed count : Nat) (outside : observed+count≤codeStart ∨ codeEnd≤observed) :
    ByteMemory.bytesAt finalState.principal.memory observed count=
      ByteMemory.bytesAt initial.principal.memory observed count := by
  rw [←StringWrites.trace_run_eq mode actual]
  unfold ByteMemory.bytesAt
  apply congrArg List.ofFn
  funext index
  apply StringWrites.run_frame mode codeStart codeEnd forms initial owned
  rcases outside with before | after
  · left;have inside:=index.isLt;omega
  · right;omega

end SmcTuring.Native.StringWriteRegions

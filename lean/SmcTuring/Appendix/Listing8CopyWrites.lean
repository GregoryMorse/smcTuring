module
public import SmcTuring.Appendix.Listing8CopyWriteBounds
public import SmcTuring.Appendix.Listing8MacroWrites

public section
namespace SmcTuring.Appendix.Listing8CopyWrites
open Native Listing8CopyImage
abbrev Placement:=Listing8CopyWriteBounds.Placement

/-- Both actual ordered copies have code-owned writes. The second Ready
and current source bytes follow from the first computed effect; they are
not future-state hypotheses. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (placed : Placement mode codeStart codeEnd l) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8CopyTrace.program mode l).map (StringWrites.liftString mode))
      (initial mode l v backing seed) := by
  have first:=Listing8MacroWrites.owned mode codeStart codeEnd (nodeParams mode l) (initial mode l v backing seed)
    (Listing8CopyTrace.first_ready mode l v resources backing seed) (Listing8CopyWriteBounds.node mode codeStart codeEnd l placed)
  have second:=Listing8MacroWrites.owned mode codeStart codeEnd (transitionParams mode l) (Listing8CopyTrace.first mode l (initial mode l v backing seed))
    (Listing8CopyTrace.second_ready mode l v resources backing seed) (Listing8CopyWriteBounds.transition mode codeStart codeEnd l placed)
  rw [Listing8CopyTrace.program,List.map_append,StringWrites.owned_run_append,StringWrites.run_lift_string,StringMacroEffects.program_run]
  exact ⟨first,second⟩

theorem copies (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (placed : Placement mode codeStart codeEnd l) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (initial mode l v backing seed) ((Listing8CopyTrace.program mode l).map (StringWrites.liftString mode))
      (Listing8CopyTrace.both mode l (initial mode l v backing seed)) ∧
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8CopyTrace.program mode l).map (StringWrites.liftString mode))
      (initial mode l v backing seed) := by
  have actual:=StringStack.previous_trace mode (StringControl.previous_trace mode (StringDword.string_trace mode (Listing8CopyTrace.copies_trace mode l v resources backing seed)))
  constructor
  · change StringStack.Trace mode (initial mode l v backing seed)
      ((Listing8CopyTrace.program mode l).map (fun form => StringStack.Form.previous (StringControl.Form.previous (StringDword.Form.string form))))
      (Listing8CopyTrace.both mode l (initial mode l v backing seed))
    simpa only [List.map_map,Function.comp_def] using actual
  · exact owned mode codeStart codeEnd l v resources placed backing seed

end SmcTuring.Appendix.Listing8CopyWrites

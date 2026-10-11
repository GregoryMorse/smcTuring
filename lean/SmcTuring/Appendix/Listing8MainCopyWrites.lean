module
public import SmcTuring.Appendix.Listing8MainCopies
public import SmcTuring.Appendix.Listing8CopyWrites
public import SmcTuring.Native.StackFieldWrites

public section
namespace SmcTuring.Appendix.Listing8MainCopyWrites
open Native Listing8CopyImage
abbrev Placement := Listing8CopyWriteBounds.Placement

/-- Both transfers own their complete stores from the same present main
image. The second readiness certificate follows from the first actual copy. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (v : Values mode)
    (resources : Resources mode l) (placed : Placement mode codeStart codeEnd l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have ready := Listing8LiveCopies.first_ready mode l resources state entry forward
    (Listing8MainCopyImage.node_current mode l v _ current)
  have next := Listing8LiveCopies.second_ready mode l resources state ready
    (Listing8MainCopyImage.rule_current mode l v _ current)
  change StringWrites.OwnedRun mode codeStart codeEnd
    (((StringProgram.forms mode l.start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size)++
      (StringProgram.forms mode (secondStart mode l) (transitionParams mode l).source
        (transitionParams mode l).destination (transitionParams mode l).size)).map (StringWrites.liftString mode)) state
  rw [List.map_append]
  apply StackFieldWrites.owned_append mode codeStart codeEnd _ _ state (Listing8CopyTrace.first mode l state)
  · change StringStack.Trace mode state
      ((StringProgram.forms mode (nodeParams mode l).start (nodeParams mode l).source
        (nodeParams mode l).destination (nodeParams mode l).size).map
          (fun form => StringStack.Form.previous (StringControl.Form.previous (StringDword.Form.string form)))) _
    simpa only [List.map_map,Function.comp_def,Listing8CopyTrace.first] using
      StringStack.previous_trace mode (StringControl.previous_trace mode
        (StringDword.string_trace mode (StringMacroTrace.trace mode _ _ ready)))
  · exact Listing8MacroWrites.owned mode codeStart codeEnd (nodeParams mode l) state ready
      (Listing8CopyWriteBounds.node mode codeStart codeEnd l placed)
  · exact Listing8MacroWrites.owned mode codeStart codeEnd (transitionParams mode l) _ next
      (Listing8CopyWriteBounds.transition mode codeStart codeEnd l placed)

theorem execute (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (v : Values mode)
    (resources : Resources mode l) (placed : Placement mode codeStart codeEnd l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringStack.Trace mode state ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode))
      (Listing8MainCopies.finish mode l state) ∧
    StringWrites.OwnedRun mode codeStart codeEnd
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  constructor
  · have actual := StringStack.previous_trace mode (StringControl.previous_trace mode
      (StringDword.string_trace mode (Listing8MainCopies.trace mode l v resources state entry forward current)))
    change StringStack.Trace mode state
      ((Listing8MainCopies.program mode l).map
        (fun form => StringStack.Form.previous (StringControl.Form.previous (StringDword.Form.string form)))) _
    simpa only [List.map_map,Function.comp_def] using actual
  · exact owned mode codeStart codeEnd l v resources placed state entry forward current

end SmcTuring.Appendix.Listing8MainCopyWrites

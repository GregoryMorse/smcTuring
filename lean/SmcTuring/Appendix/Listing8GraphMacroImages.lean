module
public import SmcTuring.Appendix.Listing8GraphMainFrames

public section
namespace SmcTuring.Appendix.Listing8GraphMacroImages
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphBackedge
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def nextLayout (mode : Mode) (origin : Nat) (l : Layout) (g : Graph)
    (node : Fin g.nodes) (rule target : Fin g.transitions) :=
  Listing8GraphCopyResources.rebound mode origin l g (Listing8GraphStep.nextNode g node rule) target

theorem node_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (finish mode origin l t g node rule memory seed).principal.memory l.start
      (StringMacroLayout.bytes mode (nodeParams mode (nextLayout mode origin l g node rule target))).length=
      StringMacroLayout.bytes mode (nodeParams mode (nextLayout mode origin l g node rule target)) := by
  apply StringMacroSource.current
  · exact Listing8GraphMainFrames.header mode origin l t g node rule ctx memory seed false
  · exact Listing8GraphMainFrames.tail mode origin l t g node rule ctx memory seed false
  · change MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory
      (StringCodec.sourceField mode l.start)=Arithmetic.encodeNat mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule))
    rw [←ctx.body.state.head.input.fields.cursorLabel]
    exact Listing8GraphBackedgeValues.head_cursor mode origin l t g node rule ctx memory seed
theorem rule_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (finish mode origin l t g node rule memory seed).principal.memory (secondStart mode l)
      (StringMacroLayout.bytes mode (transitionParams mode (nextLayout mode origin l g node rule target))).length=
      StringMacroLayout.bytes mode (transitionParams mode (nextLayout mode origin l g node rule target)) := by
  apply StringMacroSource.current
  · exact Listing8GraphMainFrames.header mode origin l t g node rule ctx memory seed true
  · exact Listing8GraphMainFrames.tail mode origin l t g node rule ctx memory seed true
  · have source:=Listing8GraphBackedgeValues.rule_cursor mode origin l t g node rule ctx memory seed
    rw [selected] at source
    exact source

end SmcTuring.Appendix.Listing8GraphMacroImages

module
public import SmcTuring.Appendix.Listing8CopyTrace

public section
namespace SmcTuring.Appendix.Listing8LiveCopies
open Native Listing8CopyImage Listing8Prototypes Listing8CopyTrace

theorem first_ready (mode : Mode) (l : Layout) (r : Resources mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (forward : state.backwards=false)
    (current : ByteMemory.bytesAt state.principal.memory l.start (StringMacroLayout.bytes mode (nodeParams mode l)).length=
      StringMacroLayout.bytes mode (nodeParams mode l)) :
    StringMacroLayout.Ready mode (nodeParams mode l) state :=
  ⟨entry,forward,r.node.sizeFits,r.node.codeFits,r.node.sourceFits,r.node.destinationFits,r.node.buffers,
    r.node.sourceOutside,r.node.destinationOutside,current⟩
theorem second_macro (mode : Mode) (l : Layout) (state : StringExecution.State mode)
    (ready : StringMacroLayout.Ready mode (nodeParams mode l) state)
    (current : ByteMemory.bytesAt state.principal.memory (secondStart mode l)
      (StringMacroLayout.bytes mode (transitionParams mode l)).length=StringMacroLayout.bytes mode (transitionParams mode l)) :
    ByteMemory.bytesAt (first mode l state).principal.memory (secondStart mode l)
      (StringMacroLayout.bytes mode (transitionParams mode l)).length=StringMacroLayout.bytes mode (transitionParams mode l) := by
  rw [first,StringMacroEffects.finish_effect mode _ _ ready,byte_frame]
  · exact current
  · right
    have ending:=(coordinates mode l).2.1
    change secondStart mode l+(StringMacroLayout.bytes mode (transitionParams mode l)).length≤(nodeParams mode l).destination
    dsimp only [nodeParams,Listing8ModeOffsets.nodeEntry,patchLayout]
    omega
theorem second_ready (mode : Mode) (l : Layout) (r : Resources mode l) (state : StringExecution.State mode)
    (ready : StringMacroLayout.Ready mode (nodeParams mode l) state)
    (current : ByteMemory.bytesAt state.principal.memory (secondStart mode l)
      (StringMacroLayout.bytes mode (transitionParams mode l)).length=StringMacroLayout.bytes mode (transitionParams mode l)) :
    StringMacroLayout.Ready mode (transitionParams mode l) (first mode l state) := by
  refine ⟨?_,?_,r.transition.sizeFits,r.transition.codeFits,r.transition.sourceFits,r.transition.destinationFits,
    r.transition.buffers,r.transition.sourceOutside,r.transition.destinationOutside,second_macro mode l state ready current⟩
  · rw [first,StringMacroEffects.finish_effect mode _ _ ready];rfl
  · rw [first,StringMacroEffects.finish_effect mode _ _ ready];exact ready.forward
theorem trace (mode : Mode) (l : Layout) (r : Resources mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (forward : state.backwards=false)
    (nodeCurrent : ByteMemory.bytesAt state.principal.memory l.start (StringMacroLayout.bytes mode (nodeParams mode l)).length=
      StringMacroLayout.bytes mode (nodeParams mode l))
    (ruleCurrent : ByteMemory.bytesAt state.principal.memory (secondStart mode l)
      (StringMacroLayout.bytes mode (transitionParams mode l)).length=StringMacroLayout.bytes mode (transitionParams mode l)) :
    StringExecution.Trace mode state (program mode l) (both mode l state) := by
  have ready:=first_ready mode l r state entry forward nodeCurrent
  exact StringExecution.trace_append mode (StringMacroTrace.trace mode _ _ ready)
    (StringMacroTrace.trace mode _ _ (second_ready mode l r state ready ruleCurrent))

/-- Snapshot bytes are read from the actual current entry state. The first
copy frames the second source; all SI/DI/SP/DF and exterior memory frames
come from the independently proved complete macro effects. -/
theorem effect (mode : Mode) (l : Layout) (r : Resources mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (forward : state.backwards=false)
    (nodeCurrent : ByteMemory.bytesAt state.principal.memory l.start (StringMacroLayout.bytes mode (nodeParams mode l)).length=
      StringMacroLayout.bytes mode (nodeParams mode l))
    (ruleCurrent : ByteMemory.bytesAt state.principal.memory (secondStart mode l)
      (StringMacroLayout.bytes mode (transitionParams mode l)).length=StringMacroLayout.bytes mode (transitionParams mode l)) :
    both mode l state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (patchStart mode l)
      accumulator:=StringInit.accumulator mode (transitionParams mode l).destination (first mode l state)
      carry:=false
      memory:=ByteMemory.putBytes
        (ByteMemory.putBytes state.principal.memory (nodeParams mode l).destination
          (ByteMemory.bytesAt state.principal.memory l.sourceNode (nodeSpan mode)))
        (transitionParams mode l).destination (ByteMemory.bytesAt state.principal.memory l.sourceTransition (transitionSpan mode))}} := by
  have ready:=first_ready mode l r state entry forward nodeCurrent
  have ruleReady:=second_ready mode l r state ready ruleCurrent
  have sourceFrame : ByteMemory.bytesAt (first mode l state).principal.memory l.sourceTransition (transitionSpan mode)=
      ByteMemory.bytesAt state.principal.memory l.sourceTransition (transitionSpan mode) := by
    rw [first,StringMacroEffects.finish_effect mode _ _ ready,byte_frame]
    have dests:=destinations mode l
    have after:=code_to_input mode l r
    simp only [ByteMemory.bytes_at_length]
    change (nodeParams mode l).destination+nodeSpan mode≤l.sourceTransition ∨
      l.sourceTransition+transitionSpan mode≤(nodeParams mode l).destination
    rcases r.transitionOutside with early | late
    · right;omega
    · left;omega
  rw [both,StringMacroEffects.finish_effect mode _ _ ruleReady]
  change _={state with principal:={state.principal with pc:=Arithmetic.encodeNat mode (patchStart mode l),accumulator:=_,carry:=false,memory:=_}}
  simp only [transitionParams]
  rw [sourceFrame,first,StringMacroEffects.finish_effect mode _ _ ready]
  rfl

end SmcTuring.Appendix.Listing8LiveCopies

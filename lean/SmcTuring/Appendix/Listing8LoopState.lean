module
public import SmcTuring.Appendix.Listing8LoopStatePrefix

public section
namespace SmcTuring.Appendix.Listing8LoopState
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopStatePrefix.Bounds
abbrev Current:=Listing8LoopStatePrefix.Current
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  Listing8StateTrace.finish mode (Listing8StateGeometry.region mode l) (Listing8LoopHead.finish mode l t v state)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  Listing8LoopHead.program mode l t v state++Listing8StateTrace.program mode (Listing8StateGeometry.region mode l) (Listing8LoopHead.finish mode l t v state)

theorem state_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringDword.Trace mode (Listing8LoopHead.finish mode l t v state)
      (Listing8StateTrace.program mode (Listing8StateGeometry.region mode l)
        (Listing8LoopHead.finish mode l t v state))
      (finish mode l t v state) :=
  Listing8StateTrace.trace mode (Listing8StateGeometry.region mode l) (Listing8StateGeometry.local_bounds mode l t b.head.input.input.prefixBounds.resources b.state) _
    (Listing8LoopHead.endpoint mode l t v old b.head state entry forward current.head)
    (Listing8LoopStatePrefix.current_after_head mode l t v old b state entry forward current).helpers
    (Listing8LoopStatePrefix.current_after_head mode l t v old b state entry forward current).headers

theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringDword.Trace mode state (program mode l t v state) (finish mode l t v state) :=
  StringDword.trace_append mode (Listing8LoopHead.trace mode l t v old b.head state entry forward current.head)
    (state_trace mode l t v old b state entry forward current)

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    (finish mode l t v state).principal.pc=
      Arithmetic.encodeNat mode (Listing8StateLayout.endPC mode (Listing8StateGeometry.region mode l)) :=
  Listing8StateTrace.endpoint mode _ (Listing8StateGeometry.local_bounds mode l t b.head.input.input.prefixBounds.resources b.state) _
    (Listing8LoopHead.endpoint mode l t v old b.head state entry forward current.head)

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :
    (program mode l t v state).length=(if mode=.x86 then 119 else 157) := by
  rw [program,List.length_append,Listing8LoopHead.instruction_count,Listing8StateTrace.instruction_count]
  cases mode <;> rfl

theorem registers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    (finish mode l t v state).principal.stack=state.principal.stack ∧
    (finish mode l t v state).sourceIndex=state.sourceIndex ∧
    (finish mode l t v state).destinationIndex=state.destinationIndex ∧
    (finish mode l t v state).backwards=false ∧
    (finish mode l t v state).principal.carry=false ∧
    (finish mode l t v state).principal.accumulator=
      DwordCode.lift mode (DwordCode.low mode (Listing8LoopHead.finish mode l t v state).principal.accumulator) := by
  have actual:=Listing8StateTrace.registers mode (Listing8StateGeometry.region mode l) (Listing8StateGeometry.local_bounds mode l t b.head.input.input.prefixBounds.resources b.state)
    (Listing8LoopHead.finish mode l t v state)
    (Listing8LoopHead.endpoint mode l t v old b.head state entry forward current.head)
  have prior:=Listing8LoopHead.registers mode l t v old b.head state entry forward current.head
  exact ⟨actual.2.1.trans prior.1,actual.2.2.2.1.trans prior.2.1,actual.2.2.2.2.1.trans prior.2.2.1,
    actual.2.2.2.2.2.trans prior.2.2.2.1,actual.2.2.1,actual.1⟩

theorem static_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory)
    (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8LoopHead.finish mode l t v state).principal.memory w.1 w.2 :=
  Listing8StateTrace.window mode (Listing8StateGeometry.region mode l) (Listing8StateGeometry.local_bounds mode l t b.head.input.input.prefixBounds.resources b.state) _
    (Listing8LoopHead.endpoint mode l t v old b.head state entry forward current.head) _ _
    (Listing8StateReuseFrames.helper_outside mode _ w member) (Listing8StateReuseFrames.packet_outside mode _ (Listing8StateGeometry.local_bounds mode l t b.head.input.input.prefixBounds.resources b.state) w member)

theorem current_after (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    Listing8LoopStateImage.Current mode (Listing8StateGeometry.region mode l) (finish mode l t v state).principal.memory :=
  Listing8LoopStateImage.transport mode _ _ _ (Listing8LoopStatePrefix.current_after_head mode l t v old b state entry forward current)
    (fun w member => static_window mode l t v old b state entry forward current w member)

theorem stack_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringStack.Trace mode state (((program mode l t v state).map StringControl.Form.previous).map StringStack.Form.previous)
      (finish mode l t v state) :=
  StringStack.previous_trace mode (StringControl.previous_trace mode (trace mode l t v old b state entry forward current))

end SmcTuring.Appendix.Listing8LoopState

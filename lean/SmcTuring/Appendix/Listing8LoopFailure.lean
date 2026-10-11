module
public import SmcTuring.Appendix.Listing8LoopFailurePrefix

public section
namespace SmcTuring.Appendix.Listing8LoopFailure
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopFailurePrefix.Bounds
abbrev Current:=Listing8LoopFailurePrefix.Current
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (state : StringExecution.State mode) :=
  Listing8FailureImage.finish mode (Listing8FailureGeometry.region mode l sentinel begin) (Listing8LoopState.finish mode l t v state)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (state : StringExecution.State mode) :=
  (Listing8LoopState.program mode l t v state).map StringControl.Form.previous++
    Listing8FailureTrace.program mode (Listing8FailureGeometry.region mode l sentinel begin) (Listing8LoopState.finish mode l t v state)
@[expose] def failed (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (state : StringExecution.State mode) :=
  Listing8FailureValues.failed mode (Listing8FailureGeometry.region mode l sentinel begin) (Listing8LoopState.finish mode l t v state).principal.memory

theorem failure_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory) :
    StringControl.Trace mode (Listing8LoopState.finish mode l t v state) (Listing8FailureTrace.program mode (Listing8FailureGeometry.region mode l sentinel begin) (Listing8LoopState.finish mode l t v state)) (finish mode l t v sentinel begin state) :=
  Listing8FailureReuseEffects.trace mode (Listing8FailureGeometry.region mode l sentinel begin) (Listing8FailureGeometry.local_bounds mode l t _ _ b.state.head.input.input.prefixBounds.resources b.failure) _
    (Listing8LoopState.endpoint mode l t v old b.state state entry forward current.state) (Listing8LoopFailurePrefix.current_after_state mode l t v old sentinel begin b state entry forward current)

theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory) :
    StringControl.Trace mode state (program mode l t v sentinel begin state) (finish mode l t v sentinel begin state) :=
  StringControl.trace_append mode (StringControl.previous_trace mode (Listing8LoopState.trace mode l t v old b.state state entry forward current.state))
    (failure_trace mode l t v sentinel begin old b state entry forward current)

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory) :
    (finish mode l t v sentinel begin state).principal.pc=Arithmetic.encodeNat mode (Listing8FailureLayout.endPC mode (Listing8FailureGeometry.region mode l sentinel begin)) :=
  Listing8FailureReuseEffects.endpoint mode (Listing8FailureGeometry.region mode l sentinel begin) (Listing8FailureGeometry.local_bounds mode l t _ _ b.state.head.input.input.prefixBounds.resources b.failure) _
    (Listing8LoopState.endpoint mode l t v old b.state state entry forward current.state) (Listing8LoopFailurePrefix.current_after_state mode l t v old sentinel begin b state entry forward current)

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (state : StringExecution.State mode) :
    (program mode l t v sentinel begin state).length=(if mode=.x86 then 132 else 173) := by
  rw [program,List.length_append,List.length_map,Listing8LoopState.instruction_count,Listing8FailureTrace.instruction_count]
  cases mode <;> rfl

theorem registers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory) :
    (finish mode l t v sentinel begin state).principal.stack=state.principal.stack ∧
    (finish mode l t v sentinel begin state).sourceIndex=state.sourceIndex ∧
    (finish mode l t v sentinel begin state).destinationIndex=state.destinationIndex ∧
    (finish mode l t v sentinel begin state).backwards=false ∧
    (finish mode l t v sentinel begin state).principal.carry=false ∧
    (finish mode l t v sentinel begin state).principal.accumulator=StringInit.accumulator mode sentinel
      (Listing8FailureImage.resetState mode (Listing8FailureGeometry.region mode l sentinel begin) (Listing8LoopState.finish mode l t v state)) := by
  have actual:=Listing8FailureReuseEffects.registers mode (Listing8FailureGeometry.region mode l sentinel begin) (Listing8FailureGeometry.local_bounds mode l t _ _ b.state.head.input.input.prefixBounds.resources b.failure) _
    (Listing8LoopState.endpoint mode l t v old b.state state entry forward current.state) (Listing8LoopFailurePrefix.current_after_state mode l t v old sentinel begin b state entry forward current)
  have prior:=Listing8LoopState.registers mode l t v old b.state state entry forward current.state
  exact ⟨actual.1.trans prior.1,actual.2.1.trans prior.2.1,actual.2.2.1.trans prior.2.2.1,
    actual.2.2.2.1.trans prior.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2⟩

theorem memory_effect (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput) (b : Bounds mode l t v sentinel begin)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory) :
    (finish mode l t v sentinel begin state).principal.memory=
      DwordCode.put (DwordCode.put (DwordCode.put (Listing8LoopState.finish mode l t v state).principal.memory (Listing8FailureLayout.andPC mode (Listing8FailureGeometry.region mode l sentinel begin)+6) (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin)))
        (Listing8FailureLayout.mask mode (Listing8FailureGeometry.region mode l sentinel begin)) (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin) &&& InputUpdate.mask (failed mode l t v sentinel begin state)))
        (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+1)
        (DwordCode.get (Listing8LoopState.finish mode l t v state).principal.memory (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+1) ^^^
          (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l sentinel begin) &&& InputUpdate.mask (failed mode l t v sentinel begin state))) :=
  Listing8FailureReuseEffects.memory mode (Listing8FailureGeometry.region mode l sentinel begin) (Listing8FailureGeometry.local_bounds mode l t _ _ b.state.head.input.input.prefixBounds.resources b.failure) _
    (Listing8LoopState.endpoint mode l t v old b.state state entry forward current.state) (Listing8LoopFailurePrefix.current_after_state mode l t v old sentinel begin b state entry forward current)

theorem current_after (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory) :
    Listing8FailureReuseImage.Current mode (Listing8FailureGeometry.region mode l sentinel begin) (finish mode l t v sentinel begin state).principal.memory :=
  Listing8FailureReuseEffects.current_after mode _ (Listing8FailureGeometry.local_bounds mode l t sentinel begin b.state.head.input.input.prefixBounds.resources b.failure) _
    (Listing8LoopState.endpoint mode l t v old b.state state entry forward current.state)
    (Listing8LoopFailurePrefix.current_after_state mode l t v old sentinel begin b state entry forward current)

theorem window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory)
    (observed count : Nat)
    (andOutside : Listing8FailureLayout.andPC mode (Listing8FailureGeometry.region mode l sentinel begin)+10≤observed ∨ observed+count≤Listing8FailureLayout.andPC mode (Listing8FailureGeometry.region mode l sentinel begin)+6)
    (maskOutside : Listing8FailureLayout.mask mode (Listing8FailureGeometry.region mode l sentinel begin)+4≤observed ∨ observed+count≤Listing8FailureLayout.mask mode (Listing8FailureGeometry.region mode l sentinel begin))
    (callOutside : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+5≤observed ∨ observed+count≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel begin)+1) :
    ByteMemory.bytesAt (finish mode l t v sentinel begin state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8LoopState.finish mode l t v state).principal.memory observed count :=
  Listing8FailureReuseEffects.window mode _ (Listing8FailureGeometry.local_bounds mode l t sentinel begin b.state.head.input.input.prefixBounds.resources b.failure) _
    (Listing8LoopState.endpoint mode l t v old b.state state entry forward current.state)
    (Listing8LoopFailurePrefix.current_after_state mode l t v old sentinel begin b state entry forward current) observed count andOutside maskOutside callOutside

theorem stack_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (old : OldInput)
    (b : Bounds mode l t v sentinel begin) (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old sentinel begin state.principal.memory) :
    StringStack.Trace mode state ((program mode l t v sentinel begin state).map StringStack.Form.previous) (finish mode l t v sentinel begin state) :=
  StringStack.previous_trace mode (trace mode l t v sentinel begin old b state entry forward current)

end SmcTuring.Appendix.Listing8LoopFailure

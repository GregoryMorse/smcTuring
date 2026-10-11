module
public import SmcTuring.Appendix.Listing8LoopDirectionPrefix

public section
namespace SmcTuring.Appendix.Listing8LoopDirection
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopDirectionPrefix.Bounds
abbrev Current:=Listing8LoopDirectionPrefix.Current
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  Listing8DirectionTrace.finish mode (Listing8DirectionGeometry.region mode l) (Listing8MainInput.finish mode l t v state)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  Listing8MainInput.program mode l t v++Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l) (Listing8MainInput.finish mode l t v state)

theorem direction_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringDword.Trace mode (Listing8MainInput.finish mode l t v state)
      (Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l) (Listing8MainInput.finish mode l t v state))
      (finish mode l t v state) := by
  have image:=Listing8LoopDirectionPrefix.current_after_input mode l t v old b state entry forward current
  exact Listing8DirectionTrace.trace mode _ b.direction.capacity _
    (Listing8MainInput.endpoint mode l t v old b.input state entry forward current.input) image.helpers image.arithmetic

theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringDword.Trace mode state (program mode l t v state) (finish mode l t v state) :=
  StringDword.trace_append mode (Listing8MainInput.trace mode l t v old b.input state entry forward current.input)
    (direction_trace mode l t v old b state entry forward current)

theorem stack_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringStack.Trace mode state (((program mode l t v state).map StringControl.Form.previous).map StringStack.Form.previous)
      (finish mode l t v state) :=
  StringStack.previous_trace mode (StringControl.previous_trace mode (trace mode l t v old b state entry forward current))

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    (finish mode l t v state).principal.pc=Arithmetic.encodeNat mode
      (Listing8DirectionLayout.selectionEnd mode (Listing8DirectionGeometry.region mode l)) :=
  Listing8DirectionTrace.endpoint mode _ b.direction.capacity _
    (Listing8MainInput.endpoint mode l t v old b.input state entry forward current.input)

theorem registers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    (finish mode l t v state).principal.stack=state.principal.stack ∧
    (finish mode l t v state).sourceIndex=state.sourceIndex ∧
    (finish mode l t v state).destinationIndex=state.destinationIndex ∧
    (finish mode l t v state).backwards=false ∧ (finish mode l t v state).principal.carry=false ∧
    (finish mode l t v state).principal.accumulator=
      DwordCode.lift mode (DwordCode.low mode (Listing8MainInput.finish mode l t v state).principal.accumulator) := by
  have actual:=Listing8DirectionTrace.registers mode _ b.direction.capacity _
    (Listing8MainInput.endpoint mode l t v old b.input state entry forward current.input)
  have prior:=Listing8MainInput.registers mode l t v old b.input state entry forward current.input
  exact ⟨actual.2.1.trans prior.1,actual.2.2.2.1.trans prior.2.1,actual.2.2.2.2.1.trans prior.2.2.1,
    actual.2.2.2.2.2.trans prior.2.2.2.1,actual.2.2.1,actual.1⟩

theorem window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (observed count : Nat)
    (helpers : ∀ writer∈Listing8DirectionLayout.helpers mode (Listing8DirectionGeometry.region mode l),
      writer.destination+4≤observed ∨ observed+count≤writer.destination)
    (arithmetic : ∀ writer∈Listing8DirectionLayout.arithmetic mode (Listing8DirectionGeometry.region mode l),
      writer.target+4≤observed ∨ observed+count≤writer.target) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory observed count=
      ByteMemory.bytesAt (Listing8MainInput.finish mode l t v state).principal.memory observed count :=
  Listing8DirectionTrace.window mode _ b.direction.capacity _
    (Listing8MainInput.endpoint mode l t v old b.input state entry forward current.input) observed count helpers arithmetic

/-- Actual direction execution retains the reusable instruction fragments. -/
theorem current_after (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l) (finish mode l t v state).principal.memory :=
  Listing8LoopDirectionImage.transport mode _ _ _ (Listing8LoopDirectionPrefix.current_after_input mode l t v old b state entry forward current)
    (fun w member => window mode l t v old b state entry forward current w.1 w.2
      (Listing8DirectionWindows.helper_outside mode _ w member) (Listing8DirectionWindows.packet_outside mode _ w member))

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :
    (program mode l t v state).length=(if mode=.x86 then 108 else 135) := by
  rw [program,List.length_append,Listing8MainInput.instruction_count,Listing8DirectionTrace.instruction_count]
  cases mode <;> rfl

end SmcTuring.Appendix.Listing8LoopDirection

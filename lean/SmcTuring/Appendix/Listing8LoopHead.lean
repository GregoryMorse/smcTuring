module
public import SmcTuring.Appendix.Listing8LoopDirection

public section
namespace SmcTuring.Appendix.Listing8LoopHead
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Bounds:=Listing8LoopDirection.Bounds
abbrev Current:=Listing8LoopDirection.Current
@[expose] def finish (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  Listing8HeadTailTrace.finish mode (Listing8DirectionGeometry.region mode l) (Listing8LoopDirection.finish mode l t v state)
@[expose] def program (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :=
  Listing8LoopDirection.program mode l t v state++Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l) (Listing8LoopDirection.finish mode l t v state)

theorem head_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringDword.Trace mode (Listing8LoopDirection.finish mode l t v state) (Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l) (Listing8LoopDirection.finish mode l t v state)) (finish mode l t v state) :=
  Listing8HeadTailTrace.trace mode (Listing8DirectionGeometry.region mode l) (Listing8HeadGeometry.tail_bounds mode l t b.direction) _
    (Listing8LoopDirection.endpoint mode l t v old b state entry forward current) (Listing8LoopDirection.current_after mode l t v old b state entry forward current).xorImage (Listing8LoopDirection.current_after mode l t v old b state entry forward current).tailHeaders

theorem trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringDword.Trace mode state (program mode l t v state) (finish mode l t v state) :=
  StringDword.trace_append mode (Listing8LoopDirection.trace mode l t v old b state entry forward current)
    (head_trace mode l t v old b state entry forward current)

theorem endpoint (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    (finish mode l t v state).principal.pc=Arithmetic.encodeNat mode (Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)) :=
  Listing8HeadTailTrace.endpoint mode (Listing8DirectionGeometry.region mode l) (Listing8HeadGeometry.tail_bounds mode l t b.direction) _
    (Listing8LoopDirection.endpoint mode l t v old b state entry forward current)

theorem instruction_count (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :
    (program mode l t v state).length=(if mode=.x86 then 113 else 145) := by
  rw [program,List.length_append,Listing8LoopDirection.instruction_count,Listing8HeadTailTrace.instruction_count]
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
      DwordCode.lift mode (DwordCode.low mode (Listing8LoopDirection.finish mode l t v state).principal.accumulator) := by
  have actual:=Listing8HeadTailTrace.registers mode (Listing8DirectionGeometry.region mode l) (Listing8HeadGeometry.tail_bounds mode l t b.direction)
    (Listing8LoopDirection.finish mode l t v state)
    (Listing8LoopDirection.endpoint mode l t v old b state entry forward current)
  have prior:=Listing8LoopDirection.registers mode l t v old b state entry forward current
  exact ⟨actual.2.1.trans prior.1,actual.2.2.2.1.trans prior.2.1,actual.2.2.2.2.1.trans prior.2.2.1,
    actual.2.2.2.2.2.trans prior.2.2.2.1,actual.2.2.1,actual.1⟩

theorem static_window (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory w.1 w.2=ByteMemory.bytesAt (Listing8LoopDirection.finish mode l t v state).principal.memory w.1 w.2 :=
  Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l) (Listing8HeadGeometry.tail_bounds mode l t b.direction) _
    (Listing8LoopDirection.endpoint mode l t v old b state entry forward current) _ _
    (Listing8DirectionWindows.xor_outside mode _ w member)
    (fun writer writerMember => Listing8DirectionWindows.tail_outside mode _
      (Listing8HeadGeometry.tail_bounds mode l t b.direction).cursorBefore w member writer (List.mem_append_left _ writerMember))
    (fun writer writerMember => Listing8DirectionWindows.tail_outside mode _
      (Listing8HeadGeometry.tail_bounds mode l t b.direction).cursorBefore w member writer (List.mem_append_right _ writerMember))

theorem current_after (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l) (finish mode l t v state).principal.memory :=
  Listing8LoopDirectionImage.transport mode _ _ _ (Listing8LoopDirection.current_after mode l t v old b state entry forward current)
    (fun w member => static_window mode l t v old b state entry forward current w member)

theorem stack_trace (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    StringStack.Trace mode state (((program mode l t v state).map StringControl.Form.previous).map StringStack.Form.previous)
      (finish mode l t v state) :=
  StringStack.previous_trace mode (StringControl.previous_trace mode (trace mode l t v old b state entry forward current))

end SmcTuring.Appendix.Listing8LoopHead

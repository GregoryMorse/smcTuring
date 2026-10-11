module
public import SmcTuring.Appendix.Listing8GraphNextDirection

public section
namespace SmcTuring.Appendix.Listing8GraphNextHead
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8HeadTailTrace.finish mode (Listing8DirectionGeometry.region mode l) (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextDirection.program mode origin l t g node rule target memory seed++
    ((Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l) (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed)).map StringControl.Form.previous).map StringStack.Form.previous

theorem xor_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8DirectionLayout.selectionEnd mode (Listing8DirectionGeometry.region mode l))
      (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l))).length=
      DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l)) := by
  have member : (Listing8DirectionLayout.selectionEnd mode (Listing8DirectionGeometry.region mode l),
      (DwordXorSequence.bytes mode (Listing8HeadTailBounds.xorLayouts mode (Listing8DirectionGeometry.region mode l))).length)∈
      Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l) := by
    simp [Listing8DirectionWindows.windows,Listing8DirectionWindows.xor_size]
  rw [Listing8GraphNextDirection.static_window mode origin l t g node rule target ctx selected memory seed _ member]
  exact Listing8GraphNextDirectionImage.xor_current mode origin l t g node rule target ctx selected memory seed

theorem tail_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordPackets.Intact mode (Listing8DirectionLayout.masks mode (Listing8DirectionGeometry.region mode l)++Listing8DirectionLayout.heads mode (Listing8DirectionGeometry.region mode l))
      (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory := by
  intro reader readerMember
  have member : (reader.pc,6)∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l) := by
    simp only [Listing8DirectionWindows.windows,List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨reader,readerMember,rfl⟩)
  rw [DwordPackets.Current,Listing8GraphNextDirection.static_window mode origin l t g node rule target ctx selected memory seed _ member]
  exact Listing8GraphNextDirectionImage.tail_current mode origin l t g node rule target ctx selected memory seed reader readerMember

theorem head_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed) (Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l) (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed)) (finish mode origin l t g node rule target memory seed) :=
  Listing8HeadTailTrace.trace mode (Listing8DirectionGeometry.region mode l) (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) _
    (Listing8GraphNextDirection.endpoint mode origin l t g node rule target ctx selected memory seed) (xor_current mode origin l t g node rule target ctx selected memory seed) (tail_current mode origin l t g node rule target ctx selected memory seed)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextDirection.trace mode origin l t g node rule target ctx selected memory seed)
    (StringStack.previous_trace mode (StringControl.previous_trace mode (head_trace mode origin l t g node rule target ctx selected memory seed)))

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)) :=
  Listing8HeadTailTrace.endpoint mode (Listing8DirectionGeometry.region mode l) (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) _
    (Listing8GraphNextDirection.endpoint mode origin l t g node rule target ctx selected memory seed)

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 260 else 340) := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphNextDirection.instruction_count,Listing8HeadTailTrace.instruction_count]
  cases mode <;> rfl

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule target memory seed).principal.accumulator=
      DwordCode.lift mode (DwordCode.low mode (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.accumulator) := by
  have actual:=Listing8HeadTailTrace.registers mode (Listing8DirectionGeometry.region mode l) (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head)
    (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed)
    (Listing8GraphNextDirection.endpoint mode origin l t g node rule target ctx selected memory seed)
  have prior:=Listing8GraphNextDirection.registers mode origin l t g node rule target ctx selected memory seed
  exact ⟨actual.2.1.trans prior.1,actual.2.2.2.1.trans prior.2.1,actual.2.2.2.2.1.trans prior.2.2.1,
    actual.2.2.2.2.2.trans prior.2.2.2.1,actual.2.2.1,actual.1⟩

theorem endpoint_offset (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=origin+(if mode=.x86 then 649 else 1029) := by
  rw [endpoint mode origin l t g node rule target ctx selected memory seed,Arithmetic.encode_nat_toNat mode _ ctx.body.state.head.capacity]
  change (Listing8StateGeometry.region mode l).start=origin+(if mode=.x86 then 649 else 1029)
  rw [(Listing8StateGeometry.positions mode l t ctx.body.state).1,ctx.boot.packed]
  cases mode <;> rfl

theorem static_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=ByteMemory.bytesAt (Listing8GraphNextDirection.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2 :=
  Listing8HeadTailTrace.window mode (Listing8DirectionGeometry.region mode l) (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) _
    (Listing8GraphNextDirection.endpoint mode origin l t g node rule target ctx selected memory seed) _ _
    (Listing8DirectionWindows.xor_outside mode _ w member)
    (fun writer writerMember => Listing8DirectionWindows.tail_outside mode _
      (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head).cursorBefore w member writer (List.mem_append_left _ writerMember))
    (fun writer writerMember => Listing8DirectionWindows.tail_outside mode _
      (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head).cursorBefore w member writer (List.mem_append_right _ writerMember))

end SmcTuring.Appendix.Listing8GraphNextHead

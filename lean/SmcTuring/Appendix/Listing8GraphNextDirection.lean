module
public import SmcTuring.Appendix.Listing8GraphNextDirectionImage

public section
namespace SmcTuring.Appendix.Listing8GraphNextDirection
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8DirectionTrace.finish mode (Listing8DirectionGeometry.region mode l)
    (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextInput.program mode origin l t g node rule target memory seed++
    ((Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l)
      (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed)).map StringControl.Form.previous).map StringStack.Form.previous

theorem direction_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed)
      (Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l)
        (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed))
      (finish mode origin l t g node rule target memory seed) :=
  Listing8DirectionTrace.trace mode (Listing8DirectionGeometry.region mode l) ctx.body.state.head.capacity _
    (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextDirectionImage.helper_current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextDirectionImage.arithmetic_current mode origin l t g node rule target ctx selected memory seed)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextInput.trace mode origin l t g node rule target ctx selected memory seed)
    (StringStack.previous_trace mode (StringControl.previous_trace mode
      (direction_trace mode origin l t g node rule target ctx selected memory seed)))

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8DirectionLayout.selectionEnd mode (Listing8DirectionGeometry.region mode l)) :=
  Listing8DirectionTrace.endpoint mode _ ctx.body.state.head.capacity _
    (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed)

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 255 else 330) := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphNextInput.instruction_count,Listing8DirectionTrace.instruction_count]
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
      DwordCode.lift mode (DwordCode.low mode (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.accumulator) := by
  have actual:=Listing8DirectionTrace.registers mode (Listing8DirectionGeometry.region mode l) ctx.body.state.head.capacity
    (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed)
    (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed)
  have prior:=Listing8GraphNextInput.registers mode origin l t g node rule target ctx selected memory seed
  exact ⟨actual.2.1.trans prior.1,actual.2.2.2.1.trans prior.2.1,actual.2.2.2.2.1.trans prior.2.2.1,
    actual.2.2.2.2.2.trans prior.2.2.2.1,actual.2.2.1,actual.1⟩

theorem endpoint_offset (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=origin+(if mode=.x86 then 611 else 953) := by
  have fits:=Nat.lt_of_le_of_lt (Listing8DirectionGeometry.positions mode l t ctx.body.state.head).2.1 ctx.body.state.head.capacity
  rw [endpoint mode origin l t g node rule target ctx selected memory seed,Arithmetic.encode_nat_toNat mode _ fits,
    (Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)).2.2.2.2.1]
  change Listing8LiteralInput.endPC mode l.input+(if mode=.x86 then 53 else 126)=origin+(if mode=.x86 then 611 else 953)
  have input:=(Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined).2.1
  rw [ctx.boot.packed] at input
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,Listing4EntryLayout.mainPC,Listing4EntryLayout.size] at input ⊢ <;> omega

theorem static_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8DirectionWindows.windows mode (Listing8DirectionGeometry.region mode l)) :
    ByteMemory.bytesAt (finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2 :=
  Listing8DirectionTrace.window mode (Listing8DirectionGeometry.region mode l) ctx.body.state.head.capacity _
    (Listing8GraphNextInput.endpoint mode origin l t g node rule target ctx selected memory seed) _ _
    (Listing8DirectionWindows.helper_outside mode _ w member) (Listing8DirectionWindows.packet_outside mode _ w member)

end SmcTuring.Appendix.Listing8GraphNextDirection

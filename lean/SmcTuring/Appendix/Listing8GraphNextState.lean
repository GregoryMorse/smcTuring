module
public import SmcTuring.Appendix.Listing8GraphNextStateImage

public section
namespace SmcTuring.Appendix.Listing8GraphNextState
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8StateTrace.finish mode (Listing8StateGeometry.region mode l)
    (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphNextHead.program mode origin l t g node rule target memory seed++
    ((Listing8StateTrace.program mode (Listing8StateGeometry.region mode l)
      (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed)).map StringControl.Form.previous).map StringStack.Form.previous

theorem state_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed)
      (Listing8StateTrace.program mode (Listing8StateGeometry.region mode l)
        (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed))
      (finish mode origin l t g node rule target memory seed) :=
  Listing8StateTrace.trace mode (Listing8StateGeometry.region mode l) (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state) _
    (Listing8GraphNextHead.endpoint mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextStateImage.helper_current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextStateImage.headers_current mode origin l t g node rule target ctx selected memory seed)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) :=
  StringStack.trace_append mode (Listing8GraphNextHead.trace mode origin l t g node rule target ctx selected memory seed)
    (StringStack.previous_trace mode (StringControl.previous_trace mode
      (state_trace mode origin l t g node rule target ctx selected memory seed)))

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8StateLayout.endPC mode (Listing8StateGeometry.region mode l)) :=
  Listing8StateTrace.endpoint mode _ (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state) _
    (Listing8GraphNextHead.endpoint mode origin l t g node rule target ctx selected memory seed)

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 266 else 352) := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphNextHead.instruction_count,Listing8StateTrace.instruction_count]
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
      DwordCode.lift mode (DwordCode.low mode (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.accumulator) := by
  have actual:=Listing8StateTrace.registers mode (Listing8StateGeometry.region mode l) (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state)
    (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed)
    (Listing8GraphNextHead.endpoint mode origin l t g node rule target ctx selected memory seed)
  have prior:=Listing8GraphNextHead.registers mode origin l t g node rule target ctx selected memory seed
  exact ⟨actual.2.1.trans prior.1,actual.2.2.2.1.trans prior.2.1,actual.2.2.2.2.1.trans prior.2.2.1,
    actual.2.2.2.2.2.trans prior.2.2.2.1,actual.2.2.1,actual.1⟩

theorem endpoint_offset (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=origin+(if mode=.x86 then 696 else 1125) := by
  rw [endpoint mode origin l t g node rule target ctx selected memory seed,Arithmetic.encode_nat_toNat mode _ ctx.body.state.capacity,
    (Listing8StateGeometry.positions mode l t ctx.body.state).2,ctx.boot.packed]
  cases mode <;> rfl

theorem static_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (w : Nat × Nat) (member : w∈Listing8StateGeometry.windows mode (Listing8StateGeometry.region mode l)) :
    ByteMemory.bytesAt (finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2=
      ByteMemory.bytesAt (Listing8GraphNextHead.finish mode origin l t g node rule target memory seed).principal.memory w.1 w.2 :=
  Listing8StateTrace.window mode (Listing8StateGeometry.region mode l) (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state) _
    (Listing8GraphNextHead.endpoint mode origin l t g node rule target ctx selected memory seed) _ _
    (Listing8StateReuseFrames.helper_outside mode _ w member) (Listing8StateReuseFrames.packet_outside mode _ (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state) w member)

end SmcTuring.Appendix.Listing8GraphNextState

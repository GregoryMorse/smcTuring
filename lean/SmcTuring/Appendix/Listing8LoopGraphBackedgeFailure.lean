module
public import SmcTuring.Appendix.Listing8LoopGraphFailure
public import SmcTuring.Appendix.Listing8GraphNextFailureImage
public import SmcTuring.Appendix.Listing8LoopGraphBackedgeState
public import SmcTuring.Appendix.Listing8LoopCallImage
public import SmcTuring.Appendix.Listing8GraphNextCallImage

public section
namespace SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
abbrev old:=Listing8LoopGraphBackedgeState.old

/-- Positive instance of the extended present-memory contract on the actual
first return, derived from the single original initialization and body. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopGraphFailure.Current mode origin (nextLayout mode origin l g node rule target) t
      (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (old mode origin g node rule)
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) :=
  ⟨Listing8LoopGraphBackedgeState.current mode origin l t g node rule target ctx selected memory seed,
    Listing8GraphNextFailureImage.after_backedge mode origin l t g node rule ctx memory seed⟩

theorem bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8LoopFailure.Bounds mode (nextLayout mode origin l g node rule target) t
      (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)
      (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) :=
  ⟨Listing8LoopGraphBackedgeState.bounds mode origin l t g node rule target ctx,
    Listing8GraphNextDirectionBounds.failure mode origin l t g node rule target ctx⟩

@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8LoopFailure.finish mode (nextLayout mode origin l g node rule target) t
    (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)
    (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
    (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphBackedge.program mode origin l t g node rule memory seed++
    ((Listing8LoopFailure.program mode (nextLayout mode origin l g node rule target) t
      (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)
      (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)).map StringStack.Form.previous)

theorem generic_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
      ((Listing8LoopFailure.program mode (nextLayout mode origin l g node rule target) t
        (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)
        (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
        (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)).map StringStack.Form.previous)
      (finish mode origin l t g node rule target memory seed) :=
  Listing8LoopGraphFailure.trace mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl
    (bounds mode origin l t g node rule target ctx) (current mode origin l t g node rule target ctx selected memory seed)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) := by
  have nonhalt : ¬Listing8GraphRun.Halted g node rule := by
    intro halted
    have none:=(Listing8GraphStep.halted_iff g node rule).mpr halted
    rw [selected] at none
    cases none
  exact StringStack.trace_append mode (Listing8GraphBackedge.trace mode origin l t g node rule ctx memory seed nonhalt)
    (generic_trace mode origin l t g node rule target ctx selected memory seed)

theorem logical_head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin (Listing8GraphStep.updated g node rule)
        (Listing8GraphStep.nextNode (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) :=
  Listing8LoopGraphFailure.logical_head mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl
    (bounds mode origin l t g node rule target ctx) (current mode origin l t g node rule target ctx selected memory seed)

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 279 else 368) := by
  rw [program,List.length_append,List.length_map,Listing8GraphBackedge.instruction_count,Listing8LoopFailure.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8FailureLayout.endPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) := by
  have now:=current mode origin l t g node rule target ctx selected memory seed
  have image:=Listing8LoopGraphFailure.input_current mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl now
  exact Listing8LoopFailure.endpoint mode _ t _ (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (old mode origin g node rule)
    (bounds mode origin l t g node rule target ctx) _ now.state.head.graph.entry now.state.head.graph.forward image

theorem retained_fragments (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8FailureReuseImage.Current mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      (finish mode origin l t g node rule target memory seed).principal.memory := by
  have now:=current mode origin l t g node rule target ctx selected memory seed
  have image:=Listing8LoopGraphFailure.input_current mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl now
  exact Listing8LoopFailure.current_after mode _ t _ (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (old mode origin g node rule)
    (bounds mode origin l t g node rule target ctx) _ now.state.head.graph.entry now.state.head.graph.forward image

theorem logical_transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (statePC mode origin (Listing8GraphStep.updated g node rule)
        (Listing8GraphStep.nextRule (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) :=
  Listing8LoopGraphFailure.logical_transition mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl
    (bounds mode origin l t g node rule target ctx) (current mode origin l t g node rule target ctx selected memory seed)

theorem failed_iff (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopFailure.failed mode (nextLayout mode origin l g node rule target) t (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)=true ↔ Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target :=
  Listing8LoopGraphFailure.failed_iff mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl
    (bounds mode origin l t g node rule target ctx) (current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphStep.native_bounds mode origin g node rule ctx.native)

theorem call_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) 5=
      Native.encode mode (.callRelative (if Listing8LoopFailure.failed mode (nextLayout mode origin l g node rule target) t (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) then 0 else Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))) := by
  have now:=current mode origin l t g node rule target ctx selected memory seed
  have image:=Listing8LoopGraphFailure.input_current mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl now
  exact Listing8LoopCallImage.call_packet mode _ t _ (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
    (old mode origin g node rule) (bounds mode origin l t g node rule target ctx) _ now.state.head.graph.entry now.state.head.graph.forward image
    (Listing8GraphNextCallImage.after_backedge mode origin l t g node rule target ctx selected memory seed)

theorem call_fetch (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringControl.fetch mode (finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))=
      some (.previous (StringDwordCopy.native mode (.callRelative (if Listing8LoopFailure.failed mode (nextLayout mode origin l g node rule target) t (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) then 0 else Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))))) :=
  StringControl.previous_fetch mode _ _ _ (StringDwordCopy.native_encoding mode _ _ _
    (call_packet mode origin l t g node rule target ctx selected memory seed))

end SmcTuring.Appendix.Listing8LoopGraphBackedgeFailure

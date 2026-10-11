module
public import SmcTuring.Appendix.Listing8LoopControlCases
public import SmcTuring.Appendix.Listing8LoopGraphContext
public import SmcTuring.Appendix.Listing8LoopBackedgeControlImage

public section
namespace SmcTuring.Appendix.Listing8LoopGraphBackedgeControl
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8LoopControl.finish mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphBackedge.program mode origin l t g node rule memory seed++Listing8LoopControl.program mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)

/-- The generic actual control theorem is positively instantiated on the
first-return memory; no future control packet or logical value is assumed. -/
theorem generic_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) (Listing8LoopControl.program mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)) (finish mode origin l t g node rule target memory seed) :=
  Listing8LoopControl.trace mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8LoopGraphContext.next mode origin l t g node rule target ctx) (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) (Listing8LoopBackedgeControlImage.current mode origin l t g node rule target ctx selected memory seed)

/-- One original initialization and its first return are followed by the
complete generic body/CALL/target path in the same memory. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) := by
  have nonhalt : ¬Listing8GraphRun.Halted g node rule := by
    intro halted
    have none:=(Listing8GraphStep.halted_iff g node rule).mpr halted
    rw [selected] at none
    cases none
  exact StringStack.trace_append mode (Listing8GraphBackedge.trace mode origin l t g node rule ctx memory seed nonhalt)
    (generic_trace mode origin l t g node rule target ctx selected memory seed)

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 286 else 377) := by
  have next:=Listing8LoopControl.instruction_count mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
  rw [program,List.length_append,Listing8GraphBackedge.instruction_count,next]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (if Listing8LoopControl.failed mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) then Listing8FullTableImage.start mode origin else l.start) :=
  Listing8LoopControl.endpoint mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8LoopGraphContext.next mode origin l t g node rule target ctx) (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) (Listing8LoopBackedgeControlImage.current mode origin l t g node rule target ctx selected memory seed)

theorem failed_iff (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopControl.failed mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)=true ↔ Listing8GraphRun.Halted (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target :=
  Listing8LoopControl.failed_iff mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8LoopGraphContext.next mode origin l t g node rule target ctx) (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) (Listing8LoopBackedgeControlImage.current mode origin l t g node rule target ctx selected memory seed)

theorem logical_head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory l.input.cursor=Arithmetic.encodeNat mode
      (nodePC mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) :=
  Listing8LoopControlFrames.logical_head mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8LoopGraphContext.next mode origin l t g node rule target ctx) (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) (Listing8LoopBackedgeControlImage.current mode origin l t g node rule target ctx selected memory seed)

theorem logical_transition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule target memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode
      (statePC mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextRule (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) :=
  Listing8LoopControlFrames.logical_transition mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8LoopGraphContext.next mode origin l t g node rule target ctx) (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) (Listing8LoopBackedgeControlImage.current mode origin l t g node rule target ctx selected memory seed)

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)) (finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) (finish mode origin l t g node rule target memory seed).principal.memory :=
by
  have actual:=Listing8LoopControlFrames.source_graph mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8LoopGraphContext.next mode origin l t g node rule target ctx) (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) (Listing8LoopBackedgeControlImage.current mode origin l t g node rule target ctx selected memory seed)
  constructor
  · exact actual.1
  · have rules:=actual.2
    rw [Listing8TransitionTable.Initial,Listing8MainGraphTable.updated_table_bytes] at rules
    exact rules

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false ∧ (finish mode origin l t g node rule target memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule target memory seed).principal.accumulator=(Listing8LoopGraphBackedgeFailure.finish mode origin l t g node rule target memory seed).principal.accumulator := by
  have prior:=Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
  have next:=Listing8LoopControl.registers mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (Listing8LoopGraphContext.next mode origin l t g node rule target ctx) (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) (Listing8LoopBackedgeControlImage.current mode origin l t g node rule target ctx selected memory seed)
  exact ⟨next.1.trans prior.2.1,next.2.1.trans prior.2.2.1,next.2.2.1.trans prior.2.2.2.1,
    next.2.2.2.1,next.2.2.2.2.1,next.2.2.2.2.2⟩

end SmcTuring.Appendix.Listing8LoopGraphBackedgeControl

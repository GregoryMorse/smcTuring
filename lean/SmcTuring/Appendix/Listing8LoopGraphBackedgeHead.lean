module
public import SmcTuring.Appendix.Listing8LoopGraphHead
public import SmcTuring.Appendix.Listing8LoopBackedgeImage
public import SmcTuring.Appendix.Listing8MainGraphBackedgeEntry

public section
namespace SmcTuring.Appendix.Listing8LoopGraphBackedgeHead
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
abbrev old:=Listing8MainGraphBackedgeEntry.old

/-- Positive instance of the extended present-memory contract on the actual
first return, derived from the single original initialization and body. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopGraphHead.Current mode origin (nextLayout mode origin l g node rule target) t
      (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (old mode origin g node rule)
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) :=
  ⟨Listing8MainGraphBackedgeEntry.current mode origin l t g node rule target ctx selected memory seed,
    Listing8LoopBackedgeImage.current mode origin l t g node rule ctx memory seed⟩

theorem bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8LoopHead.Bounds mode (nextLayout mode origin l g node rule target) t
      (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) :=
  ⟨Listing8MainGraphBackedgeEntry.bounds mode origin l t g node rule target ctx,
    Listing8GraphNextDirectionBounds.direction mode origin l t g node rule target ctx⟩

@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8LoopHead.finish mode (nextLayout mode origin l g node rule target) t
    (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)
    (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphBackedge.program mode origin l t g node rule memory seed++
    (((Listing8LoopHead.program mode (nextLayout mode origin l g node rule target) t
      (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)).map StringControl.Form.previous).map StringStack.Form.previous)

theorem generic_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
      (((Listing8LoopHead.program mode (nextLayout mode origin l g node rule target) t
        (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)
        (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)).map StringControl.Form.previous).map StringStack.Form.previous)
      (finish mode origin l t g node rule target memory seed) :=
  Listing8LoopGraphHead.trace mode origin (nextLayout mode origin l g node rule target) t
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
  Listing8LoopGraphHead.logical_head mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl
    (bounds mode origin l t g node rule target ctx) (current mode origin l t g node rule target ctx selected memory seed)

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 260 else 340) := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphBackedge.instruction_count,Listing8LoopHead.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)) := by
  have now:=current mode origin l t g node rule target ctx selected memory seed
  have image:=Listing8LoopGraphHead.input_current mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl now
  exact Listing8LoopHead.endpoint mode _ t _ (old mode origin g node rule)
    (bounds mode origin l t g node rule target ctx) _ now.graph.entry now.graph.forward image

theorem retained_fragments (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l)
      (finish mode origin l t g node rule target memory seed).principal.memory := by
  have now:=current mode origin l t g node rule target ctx selected memory seed
  have image:=Listing8LoopGraphHead.input_current mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl now
  exact Listing8LoopHead.current_after mode _ t _ (old mode origin g node rule)
    (bounds mode origin l t g node rule target ctx) _ now.graph.entry now.graph.forward image

end SmcTuring.Appendix.Listing8LoopGraphBackedgeHead

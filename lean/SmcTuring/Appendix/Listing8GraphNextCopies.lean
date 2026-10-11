module
public import SmcTuring.Appendix.Listing8GraphMacroImages
public import SmcTuring.Appendix.Listing8LiveCopies

public section
namespace SmcTuring.Appendix.Listing8GraphNextCopies
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphBackedge.program mode origin l t g node rule memory seed++
    (((Listing8CopyTrace.program mode (nextLayout mode origin l g node rule target)).map StringDword.Form.string).map
      StringControl.Form.previous).map StringStack.Form.previous
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8CopyTrace.both mode (nextLayout mode origin l g node rule target)
    (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)

theorem resources (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Resources mode (nextLayout mode origin l g node rule target) :=
  Listing8GraphCopyResources.resources mode origin l t g node rule ctx (Listing8GraphStep.nextNode g node rule) target
theorem copy_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringExecution.Trace mode (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
      (Listing8CopyTrace.program mode (nextLayout mode origin l g node rule target))
      (finish mode origin l t g node rule target memory seed) := by
  have regs:=Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
  exact Listing8LiveCopies.trace mode _ (resources mode origin l t g node rule target ctx) _ regs.1 regs.2.2.2.2.1
    (node_current mode origin l t g node rule target ctx memory seed)
    (rule_current mode origin l t g node rule target ctx selected memory seed)
/-- The actual first pass and backedge are followed by both next-pass
copies on the same mutated memory. All next Ready and source packets are
derived; no initializer is inserted between passes. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) := by
  have nonhalt : ¬Listing8GraphRun.Halted g node rule := by
    intro halted
    have none:=(Listing8GraphStep.halted_iff g node rule).mpr halted
    rw [selected] at none
    cases none
  have first:=Listing8GraphBackedge.trace mode origin l t g node rule ctx memory seed nonhalt
  have last:=StringStack.previous_trace mode (StringControl.previous_trace mode
    (StringDword.string_trace mode (copy_trace mode origin l t g node rule target ctx selected memory seed)))
  exact StringStack.trace_append mode first last
theorem source_packets (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let next:=nextLayout mode origin l g node rule target
    let v:=values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    let state:=Listing8GraphBackedge.finish mode origin l t g node rule memory seed
    ByteMemory.bytesAt state.principal.memory next.sourceNode (nodeSpan mode)=sourceNodeBytes mode next v ∧
    ByteMemory.bytesAt state.principal.memory next.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode next v :=
  ⟨Listing8GraphBackedgeSources.node_current mode origin l t g node rule ctx memory seed (Listing8GraphStep.nextNode g node rule),
    Listing8GraphBackedgeSources.rule_current mode origin l t g node rule ctx memory seed target (Listing8GraphStep.nextNode g node rule)⟩
theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let next:=nextLayout mode origin l g node rule target
    let v:=values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    let state:=Listing8GraphBackedge.finish mode origin l t g node rule memory seed
    finish mode origin l t g node rule target memory seed={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (patchStart mode l)
      accumulator:=StringInit.accumulator mode (transitionParams mode next).destination (Listing8CopyTrace.first mode next state)
      carry:=false
      memory:=ByteMemory.putBytes (ByteMemory.putBytes state.principal.memory (nodeParams mode next).destination (sourceNodeBytes mode next v))
        (transitionParams mode next).destination (sourceTransitionBytes mode next v)}} := by
  have regs:=Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
  have result:=Listing8LiveCopies.effect mode _ (resources mode origin l t g node rule target ctx) _ regs.1 regs.2.2.2.2.1
    (node_current mode origin l t g node rule target ctx memory seed)
    (rule_current mode origin l t g node rule target ctx selected memory seed)
  have packets:=source_packets mode origin l t g node rule target ctx memory seed
  rw [packets.1,packets.2] at result
  exact result
theorem copied_packets (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let next:=nextLayout mode origin l g node rule target
    let v:=values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    ByteMemory.bytesAt (finish mode origin l t g node rule target memory seed).principal.memory (nodeParams mode next).destination
      (sourceNodeBytes mode next v).length=sourceNodeBytes mode next v ∧
    ByteMemory.bytesAt (finish mode origin l t g node rule target memory seed).principal.memory (transitionParams mode next).destination
      (sourceTransitionBytes mode next v).length=sourceTransitionBytes mode next v := by
  rw [effect mode origin l t g node rule target ctx selected memory seed]
  constructor
  · rw [byte_frame _ _ _ _ _ (Or.inr (by
      rw [show (sourceNodeBytes mode _ _).length=nodeSpan mode from node_length mode _ _ _ _]
      exact (destinations mode _).2.1.le))]
    exact ByteMemory.bytes_at_put _ _ _
  · exact ByteMemory.bytes_at_put _ _ _
theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 192 else 242) := by
  have copies : (Listing8CopyTrace.program mode (nextLayout mode origin l g node rule target)).length=(if mode=.x86 then 45 else 47) := by
    cases mode <;> simp [Listing8CopyTrace.program,StringProgram.forms,StringSetup.forms,StringSetup.sourceForms,
      StringInit.forms,StringMoves.forms,StringRestore.forms,StringPlan.widths,nodeParams,transitionParams,
      nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize]
  rw [program,List.length_append,List.length_map,List.length_map,List.length_map,Listing8GraphBackedge.instruction_count,copies]
  cases mode <;> rfl
theorem run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (nonhalt : ¬Listing8GraphRun.Halted g node rule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ target : Fin g.transitions,Listing8GraphStep.nextRule g node rule=some target ∧
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
        (program mode origin l t g node rule target memory seed) (finish mode origin l t g node rule target memory seed) ∧
      (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 192 else 242) := by
  obtain ⟨target,selected⟩:=Listing8GraphLabels.nonhalt_rule g node rule nonhalt
  exact ⟨target,selected,trace mode origin l t g node rule target ctx selected memory seed,
    instruction_count mode origin l t g node rule target memory seed⟩

end SmcTuring.Appendix.Listing8GraphNextCopies

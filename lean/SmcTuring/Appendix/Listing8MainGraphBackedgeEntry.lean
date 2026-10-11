module
public import SmcTuring.Appendix.Listing8MainGraphImage
public import SmcTuring.Appendix.Listing8MainGraphTable
public import SmcTuring.Appendix.Listing8GraphNextHelperImage
public import SmcTuring.Appendix.Listing8GraphNextInputBounds
public import SmcTuring.Appendix.Listing8GraphBackedgeInput

public section
namespace SmcTuring.Appendix.Listing8MainGraphBackedgeEntry
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def old (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) : Listing8MainInput.OldInput :=
  let v:=values mode origin g node rule
  ⟨-(v.rule-v.tape),v.tape,Listing8GraphBackedgeInput.pending mode origin g node rule,v.fresh,Listing8GraphBackedgeInput.mask mode origin g node rule⟩

/-- The generic current-state contract is established on the actual first
returned memory, including the whole updated graph and original rule bytes. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8MainGraphImage.Current mode origin (nextLayout mode origin l g node rule target) t
      (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target (old mode origin g node rule)
      (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) := by
  have registers:=Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
  refine ⟨registers.1,registers.2.2.2.2.1,
    Listing8MainCopyImage.macro_from_packet mode _ _ (Listing8GraphMacroImages.node_current mode origin l t g node rule target ctx memory seed),
    Listing8MainCopyImage.macro_from_packet mode _ _ (Listing8GraphMacroImages.rule_current mode origin l t g node rule target ctx selected memory seed),
    ?_,Listing8GraphNextHelperImage.after_backedge mode origin l t g node rule ctx memory seed,?_,
    Listing8GraphBackedgeSources.nodes_initial mode origin l t g node rule ctx memory seed,
    Listing8MainGraphTable.updated_table_current mode origin g node rule _ (Listing8GraphBackedgeSources.table_current mode origin l t g node rule ctx memory seed)⟩
  · rw [Listing8GraphPatchBlock.patch_length]
    exact Listing8GraphPatchBlock.after_backedge mode origin l t g node rule ctx memory seed
  · change Listing8InputMask.Intact mode
      {l.input with head:=nodePC mode origin g (Listing8GraphStep.nextNode g node rule)}
      (-((values mode origin g node rule).rule-(values mode origin g node rule).tape)) (values mode origin g node rule).tape
      (Listing8GraphBackedgeInput.pending mode origin g node rule) (values mode origin g node rule).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule) _
    rw [Listing8InputMask.Intact,Listing8InputReuseFields.head_bytes]
    exact Listing8GraphBackedgeInput.current mode origin l t g node rule ctx memory seed

/-- Every generic next-pass bound follows from original layout/capacity
certificates and the logical selected labels; no memory/Ready fact is used. -/
theorem bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8MainInput.Bounds mode (nextLayout mode origin l g node rule target) t
      (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target) := by
  refine ⟨⟨⟨Listing8GraphNextCopies.resources mode origin l t g node rule target ctx,
    Listing8GraphNextOwnerBounds.owner_bounds mode origin l t g node rule target ctx,
    Listing8GraphNextOwnerBounds.pointer_copies mode origin l t g node rule target ctx,
    Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx,
    ctx.body.state.head.input.joined,ctx.fields.tapeReach⟩,ctx.body.state.head.input.targetsAfter⟩,?_⟩
  intro writer member
  have after:=Nat.le_trans (Listing8GraphNextPointerFrames.failure_before_table mode origin l t g node rule ctx)
    (Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule))
  exact Or.inl (Listing8FailureGeometry.pointer_outside mode l t _ _ ctx.body _ after writer member)

@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8MainInput.finish mode (nextLayout mode origin l g node rule target) t
    (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)
    (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphBackedge.program mode origin l t g node rule memory seed++
    (((Listing8MainInput.program mode (nextLayout mode origin l g node rule target) t
      (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)).map
      StringControl.Form.previous).map StringStack.Form.previous)

theorem generic_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
      (((Listing8MainInput.program mode (nextLayout mode origin l g node rule target) t
        (values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target)).map
        StringControl.Form.previous).map StringStack.Form.previous) (finish mode origin l t g node rule target memory seed) :=
  Listing8MainGraphImage.trace mode origin (nextLayout mode origin l g node rule target) t
    (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    (old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) rfl rfl
    (bounds mode origin l t g node rule target ctx) (current mode origin l t g node rule target ctx selected memory seed)

/-- This connects the reusable arbitrary-entry theorem to the single
original initialization. There is no host initialization between the traces. -/
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

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule target memory seed).length=(if mode=.x86 then 248 else 313) := by
  rw [program,List.length_append,List.length_map,List.length_map,Listing8GraphBackedge.instruction_count,Listing8MainInput.instruction_count]
  cases mode <;> rfl

end SmcTuring.Appendix.Listing8MainGraphBackedgeEntry

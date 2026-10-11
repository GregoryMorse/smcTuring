module
public import SmcTuring.Appendix.Listing8CopyOwnerFinal
public import SmcTuring.Appendix.Listing8GraphCopyFetch
public import SmcTuring.Appendix.Listing8GraphNextCopies

public section
namespace SmcTuring.Appendix.Listing8GraphCopyOwnerPrefixes
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem original_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8MainCopyImage.Current mode l (values mode origin g node rule)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.memory := by
  rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
  apply Listing8MainCopyImage.from_packets
  · exact initial_node_macro mode l _ ctx.resources _
  · exact initial_transition_macro mode l _ ctx.resources _
  · exact initial_patches mode l _ ctx.resources _
  · simpa only [initial,sourceNodeBytes,Listing8Prototypes.node_length] using initial_source_node mode l (values mode origin g node rule) ctx.resources (Listing8GraphCopyWrites.copyBacking mode origin l t g memory)
  · simpa only [initial,sourceTransitionBytes,Listing8Prototypes.transition_length] using initial_source_transition mode l (values mode origin g node rule) (Listing8GraphCopyWrites.copyBacking mode origin l t g memory)

theorem original (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)
      (Listing8GraphCopyWrites.copyForms mode l) (Listing8GraphCopyWrites.finish mode origin l t g node rule memory seed) ∧
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphCopyWrites.copyForms mode l) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8GraphCopyWrites.copyForms mode l) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) ∧
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphCopyWrites.copyForms mode l) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) ∧
    Listing8CopyOwnerPrefixes.Both mode l (values mode origin g node rule) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) ∧
    Listing8CopyOwnerFinal.Final mode (nodeParams mode l) (Listing8CopyOwnerPrefixes.nodeTemplates mode l (values mode origin g node rule))
      (Listing8GraphCopyWrites.finish mode origin l t g node rule memory seed).principal.memory ∧
    Listing8CopyOwnerFinal.Final mode (transitionParams mode l) (Listing8CopyOwnerPrefixes.transitionTemplates mode l (values mode origin g node rule))
      (Listing8GraphCopyWrites.finish mode origin l t g node rule memory seed).principal.memory := by
  have access := Listing8GraphCopyFetch.original mode origin l t g node rule ctx memory seed
  have current := original_current mode origin l t g node rule ctx memory seed
  have entry : (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode l.start := by
    rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  have forward : (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).backwards=false := by
    rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  refine ⟨access.1,access.2.1,access.2.2.1,access.2.2.2,?_,?_,?_⟩
  · exact Listing8CopyOwnerPrefixes.pair mode l _ ctx.resources _ entry forward
      (Listing8MainCopyImage.node_current mode l _ _ current) (Listing8MainCopyImage.rule_current mode l _ _ current) current.node current.rule
  · exact Listing8CopyOwnerFinal.node mode l _ ctx.resources _ entry forward current
  · exact Listing8CopyOwnerFinal.transition mode l _ ctx.resources _ entry forward current

theorem live (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStack.Trace mode state ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) (Listing8MainCopies.finish mode l state) ∧
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state ∧
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state ∧
    Listing8CopyOwnerPrefixes.Both mode l (values mode origin g node rule) (state) ∧
    Listing8CopyOwnerFinal.Final mode (nodeParams mode l) (Listing8CopyOwnerPrefixes.nodeTemplates mode l (values mode origin g node rule))
      (Listing8MainCopies.finish mode l state).principal.memory ∧
    Listing8CopyOwnerFinal.Final mode (transitionParams mode l) (Listing8CopyOwnerPrefixes.transitionTemplates mode l (values mode origin g node rule))
      (Listing8MainCopies.finish mode l state).principal.memory := by
  have access := Listing8GraphCopyFetch.live mode origin l t g node rule ctx state entry forward current
  refine ⟨access.1,access.2.1,access.2.2.1,access.2.2.2,?_,?_,?_⟩
  · exact Listing8CopyOwnerPrefixes.pair mode l _ ctx.resources state entry forward
      (Listing8MainCopyImage.node_current mode l _ _ current) (Listing8MainCopyImage.rule_current mode l _ _ current) current.node current.rule
  · exact Listing8CopyOwnerFinal.node mode l _ ctx.resources state entry forward current
  · exact Listing8CopyOwnerFinal.transition mode l _ ctx.resources state entry forward current

/-- The actual selected backedge derives the next source packets, macro
entries and all copy-prefix templates. No later image is a hypothesis. -/
theorem next_prefixes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let next := Listing8GraphMacroImages.nextLayout mode origin l g node rule target
    let v := values mode origin (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (Listing8GraphNextCopies.program mode origin l t g node rule target memory seed)
      (Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed) ∧
    Listing8CopyOwnerPrefixes.Both mode next v (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) := by
  have registers := Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
  have sources := Listing8GraphNextCopies.source_packets mode origin l t g node rule target ctx memory seed
  refine ⟨Listing8GraphNextCopies.trace mode origin l t g node rule target ctx selected memory seed,?_⟩
  exact Listing8CopyOwnerPrefixes.pair mode _ _ (Listing8GraphNextCopies.resources mode origin l t g node rule target ctx)
    _ registers.1 registers.2.2.2.2.1
    (Listing8GraphMacroImages.node_current mode origin l t g node rule target ctx memory seed)
    (Listing8GraphMacroImages.rule_current mode origin l t g node rule target ctx selected memory seed)
    sources.1 sources.2

end SmcTuring.Appendix.Listing8GraphCopyOwnerPrefixes

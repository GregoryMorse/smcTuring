module
public import SmcTuring.Appendix.Listing8GraphNextRetarget
public import SmcTuring.Appendix.Listing8LiveOwnerImage

public section
namespace SmcTuring.Appendix.Listing8GraphNextOwnerImage
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem source_packets (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let next:=nextLayout mode origin l g node rule target
    let v:=liveValues mode origin g node rule target
    let state:=Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed
    ByteMemory.bytesAt state.principal.memory next.sourceNode (sourceNodeBytes mode next v).length=sourceNodeBytes mode next v ∧
    ByteMemory.bytesAt state.principal.memory next.sourceTransition (sourceTransitionBytes mode next v).length=sourceTransitionBytes mode next v := by
  have prior:=Listing8GraphNextCopies.source_packets mode origin l t g node rule target ctx memory seed
  have before:=Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g (Listing8GraphStep.nextNode g node rule)
  have ruleAfter:=Listing8GraphLayout.transition_lower mode origin target.val
  constructor
  · rw [Listing8GraphNextCopyFrames.window mode origin l t g node rule target ctx selected memory seed
      (nextLayout mode origin l g node rule target).sourceNode
      (sourceNodeBytes mode (nextLayout mode origin l g node rule target) (liveValues mode origin g node rule target)).length
      (Nat.le_trans before nodeAfter)]
    simpa only [sourceNodeBytes,node_length,liveValues] using prior.1
  · rw [Listing8GraphNextCopyFrames.window mode origin l t g node rule target ctx selected memory seed
      (nextLayout mode origin l g node rule target).sourceTransition
      (sourceTransitionBytes mode (nextLayout mode origin l g node rule target) (liveValues mode origin g node rule target)).length
      (Nat.le_trans before ruleAfter)]
    simpa only [sourceTransitionBytes,transition_length,liveValues] using prior.2
/-- The whole seven-owner image is derived after the actual copies and
retargets; no future owner image or readiness is a hypothesis. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8OwnerSequence.Intact mode (Listing8OwnerImage.owners mode (nextLayout mode origin l g node rule target)
      (liveValues mode origin g node rule target)) (finish mode origin l t g node rule target memory seed).principal.memory := by
  have sources:=source_packets mode origin l t g node rule target ctx selected memory seed
  exact Listing8LiveOwnerImage.current mode _ _ (Listing8GraphNextCopies.resources mode origin l t g node rule target ctx)
    ctx.fields.tapeReach _ (Listing8GraphNextCopyFrames.registers mode origin l t g node rule target ctx selected memory seed).1
    (Listing8GraphPatchBlock.current mode origin l t g node rule target ctx selected memory seed) sources.1 sources.2

end SmcTuring.Appendix.Listing8GraphNextOwnerImage

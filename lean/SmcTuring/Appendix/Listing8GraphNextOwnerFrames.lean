module
public import SmcTuring.Appendix.Listing8GraphNextOwners

public section
namespace SmcTuring.Appendix.Listing8GraphNextOwnerFrames
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem live_frame (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat)
    (patches : ∀ site∈Listing8ModeOffsets.sites mode (patchLayout mode l),site.owner+6≤observed ∨ observed+count≤site.owner+2)
    (tape : Listing8LiteralInput.sourceField mode l.input+4≤observed ∨ observed+count≤Listing8LiteralInput.sourceField mode l.input)
    (ruleField : Listing8LiteralInput.scalarField mode l.input+4≤observed ∨ observed+count≤Listing8LiteralInput.scalarField mode l.input)
    (fresh : Listing8LiteralInput.updateStart mode l.input+10≤observed ∨ observed+count≤Listing8LiteralInput.updateStart mode l.input+6)
    (direction : l.direction+10≤observed ∨ observed+count≤l.direction+6) :
    ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed).principal.memory observed count := by
  rw [(Listing8GraphNextOwners.result mode origin l t g node rule target ctx selected memory seed).2.1,
    DwordMixedImage.bytes_frame _ _ _ _ _ direction,DwordMixedImage.bytes_frame _ _ _ _ _ fresh,
    DwordMixedImage.bytes_frame _ _ _ _ _ ruleField]
  exact Listing8LiveRetarget.frame mode _ _ (Listing8GraphNextCopies.resources mode origin l t g node rule target ctx)
    ctx.fields.tapeReach _ (Listing8GraphNextCopyFrames.registers mode origin l t g node rule target ctx selected memory seed).1
    observed count patches tape

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : Listing8FullTableImage.start mode origin≤observed) :
    ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  have fields:=Listing8CopiedOwners.scalar_bounds mode l
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have before:=Listing8GraphCopyResources.input_before_table mode origin l t g node rule ctx
  have codeBefore:=Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have direction:=Listing8GraphNextOwnerBounds.direction_before_table mode origin l t g node rule ctx
  rw [live_frame mode origin l t g node rule target ctx selected memory seed observed count
    (fun site member => Or.inl (by
      have bounds:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).2.1
      change site.owner+10≤codeEnd mode l at bounds;omega))
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
  exact Listing8GraphNextCopyFrames.window mode origin l t g node rule target ctx selected memory seed observed count (by omega)

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory := by
  have inputBefore:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions)
    (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,window mode origin l t g node rule target ctx selected memory seed _ _ inputBefore]
    exact Listing8GraphBackedgeSources.nodes_initial mode origin l t g node rule ctx memory seed
  · rw [Listing8TransitionTable.Initial,window mode origin l t g node rule target ctx selected memory seed _ _ (Nat.le_refl _)]
    exact Listing8GraphBackedgeSources.table_current mode origin l t g node rule ctx memory seed

end SmcTuring.Appendix.Listing8GraphNextOwnerFrames

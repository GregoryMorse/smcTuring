module
public import SmcTuring.Appendix.Listing8OriginalGraphBootstrap

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphMainEntry
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def old : Listing8MainInput.OldInput:=⟨0,force,force,force,force⟩

theorem nodes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin g)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.memory := by
  have after : Listing8FullTableImage.start mode origin≤Listing8GraphLayout.input mode origin g.transitions := by
    have lower:=Listing8GraphLayout.transition_lower mode origin g.transitions
    change Listing8FullTableImage.start mode origin≤Listing8GraphLayout.reset mode origin g.transitions at lower
    exact lower.trans (Listing8GraphLayout.table_before_input mode origin g.transitions)
  rw [Listing8NodeTable.Initial,Listing8OriginalGraphBootstrap.window mode origin l t g node rule ctx memory seed _ _ after]
  exact Listing8OriginalGraphBootstrap.nodes_initial mode origin l t g node rule ctx memory

theorem rules (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.memory := by
  rw [Listing8TransitionTable.Initial,Listing8OriginalGraphBootstrap.window mode origin l t g node rule ctx memory seed _ _ (Nat.le_refl _)]
  exact Listing8OriginalGraphBootstrap.rules_initial mode origin l t g node rule ctx memory

/-- Actual bootstrap and original emission supply the full present graph,
macro,cursor,helper and input contract for the first generic main pass. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8MainGraphImage.Current mode origin l t g node rule old
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have copies:=Listing8GlobalOriginalPrefix.copying mode origin l t g node rule ctx memory seed
  refine ⟨?_,?_,copies.nodeMacro,copies.ruleMacro,copies.patches,
    (Listing8GlobalOriginalPrefix.current mode origin l t g node rule ctx memory seed).helpers,?_,
    nodes mode origin l t g node rule ctx memory seed,rules mode origin l t g node rule ctx memory seed⟩
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  · rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
    exact initial_input mode l _ ctx.resources _

end SmcTuring.Appendix.Listing8OriginalGraphMainEntry

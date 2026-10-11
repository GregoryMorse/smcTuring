module
public import SmcTuring.Appendix.Listing8GraphBodyFetch

public section
namespace SmcTuring.Appendix.Listing8GraphEntryFetch
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringPCWindows.Run StringFetchWindows.Run StringWrites.OwnedRun StringReadRuns.Run

theorem split (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphJumpWrites.program mode origin l t g node rule memory seed=
      Listing8GraphFailureWrites.program mode origin l t g node rule memory seed++
      Listing8JumpLayout.forms mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed) := by
  simp only [Listing8GraphJumpWrites.program,Listing8GraphJumpWrites.forms,Listing8GraphFailureWrites.program,List.append_assoc]

theorem windows (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringPCWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  rw [split]
  exact StringPCWindows.append_trace mode _ _ _ _ (Listing8GraphFailureWrites.finish mode origin l t g node rule memory seed)
    (Listing8GraphFailureWrites.execute mode origin l t g node rule ctx memory seed).1
    (Listing8GraphBodyFetch.windows mode origin l t g node rule ctx memory seed)
    (Listing8JumpPCWindows.jump mode origin _ origin _ _
      (Listing8GraphBodyFetch.endpoint mode origin l t g node rule ctx memory seed)
      (Listing8LoopReturnFetch.placement mode origin g.transitions g.nodes _) ctx.native.capacity)

theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  StringFetchWindows.of_pc_run mode _ (Listing8GraphJumpWrites.trace mode origin l t g node rule ctx memory seed)
    (windows mode origin l t g node rule ctx memory seed)

theorem complete (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed) (Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed) ∧
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) ∧
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  ⟨(Listing8GraphEntryWrites.execute mode origin l t g node rule ctx memory seed).1,
    contained mode origin l t g node rule ctx memory seed,
    (Listing8GraphEntryWrites.execute mode origin l t g node rule ctx memory seed).2,
    Listing8GraphEntryReads.contained mode origin l t g node rule ctx memory seed⟩

end SmcTuring.Appendix.Listing8GraphEntryFetch

module
public import SmcTuring.Appendix.Listing8CopyFetch
public import SmcTuring.Appendix.Listing8GraphCopyWrites

public section
namespace SmcTuring.Appendix.Listing8GraphCopyFetch
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

/-- The actual bootstrap result enters both original graph copies. Context
derives code placement and numeric capacity; no later window is supplied. -/
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
      (Listing8GraphCopyWrites.copyForms mode l) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have actual:=Listing8GraphCopyWrites.copies mode origin l t g node rule ctx memory seed
  refine ⟨actual.1,?_,actual.2,?_⟩
  · unfold Listing8GraphCopyWrites.copyForms
    rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
    exact Listing8CopyFetch.original mode origin _ l _ ctx.resources
      (Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx) ctx.native.capacity _ _
  · unfold Listing8GraphCopyWrites.copyForms
    rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
    exact Listing8CopyReads.original mode origin _ l _ ctx.resources
      (Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx) _ _

/-- The same certificates cover the two maintained live graph transfers;
original graph labels derive every placement and bound. -/
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
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state :=
  Listing8CopyFetch.complete_live mode origin _ l _ ctx.resources
    (Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx) ctx.native.capacity state entry forward current

end SmcTuring.Appendix.Listing8GraphCopyFetch

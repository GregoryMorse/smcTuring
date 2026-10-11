module
public import SmcTuring.Appendix.Listing8JumpFetch
public import SmcTuring.Appendix.Listing8LoopControl

public section
namespace SmcTuring.Appendix.Listing8LoopReturnFetch
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem table_before_end (mode : Mode) (origin transitions nodes : Nat) :
    Listing8FullTableImage.start mode origin≤Listing8GraphLayout.endPC mode origin transitions nodes := by
  dsimp [Listing8GraphLayout.endPC,Listing8GraphLayout.node,Listing8GraphLayout.input,
    Listing8GraphLayout.reset,Listing8GraphLayout.transition]
  omega

/-- Original packed geometry bounds both possible CALL destinations and the
complete target helpers, independently of any runtime or future trace. -/
theorem placement (mode : Mode) (origin transitions nodes : Nat) (failed : Bool) :
    Listing8JumpPCWindows.Placement mode origin (Listing8GraphLayout.endPC mode origin transitions nodes) origin failed := by
  have table:=table_before_end mode origin transitions nodes
  have failBefore : Listing8JumpLayout.failPC mode origin≤Listing8FullTableImage.start mode origin := by
    dsimp [Listing8FullTableImage.start,Listing8FailLayout.endPC]
    omega
  refine ⟨⟨?_,Nat.le_trans failBefore table⟩,?_,?_⟩
  · dsimp [Listing8JumpLayout.jumpPC];omega
  · have afterStack:=Listing8JumpReturn.placement mode origin failed;omega
  · cases failed with
    | false =>
      change Listing8BootImage.beginPC mode origin+Listing4TargetLayout.size mode≤_
      have endpoint:=Listing4EntryLayout.endpoint mode origin
      have position:=(Listing4TargetLayout.positions mode (Listing8BootImage.beginPC mode origin)).2.2.2
      change Listing4TargetLayout.endPC mode (Listing8BootImage.beginPC mode origin)=Listing4EntryLayout.mainPC mode origin at endpoint
      rw [position] at endpoint
      rw [endpoint]
      apply Nat.le_trans _ table
      rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset]
      cases mode <;> dsimp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size] <;> omega
    | true => exact table

/-- The actual maintained loop invariant derives current jump packets,
entry and both fetch/target bounds from original graph geometry. -/
theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.failureEnd mode origin l t g node rule state) :=
  Listing8JumpFetch.contained mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) origin _ _
    (Listing8LoopControl.entry mode origin l t g node rule ctx old state image)
    (placement mode origin g.transitions g.nodes _) ctx.native.capacity
    (Listing8LoopControl.current mode origin l t g node rule ctx old state image)

theorem complete (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    StringStack.Trace mode (Listing8LoopControl.failureEnd mode origin l t g node rule state)
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.finish mode origin l t g node rule state) ∧
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.failureEnd mode origin l t g node rule state) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.failureEnd mode origin l t g node rule state) ∧
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8JumpReturn.program mode origin (Listing8LoopControl.failed mode origin l t g node rule state))
      (Listing8LoopControl.failureEnd mode origin l t g node rule state) := by
  have placed:=placement mode origin g.transitions g.nodes (Listing8LoopControl.failed mode origin l t g node rule state)
  exact Listing8JumpFetch.complete mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) origin _ _
    (Listing8LoopControl.entry mode origin l t g node rule ctx old state image) placed ctx.native.capacity
    ⟨Nat.le_refl _,Nat.le_trans (Listing8FailLayout.placement mode origin) placed.jump.2⟩
    (Listing8LoopControl.current mode origin l t g node rule ctx old state image)

theorem target_access (mode : Mode) (environment : MappedExecution.Environment) (origin : Nat)
    (l : Layout) (t : Targets) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (mapping : MappedExecution.Mapped mode environment ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩)
    (ctx : Context mode origin l t g node rule) (old : OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControl.Current mode origin l t g node rule old state) :
    let failed:=Listing8LoopControl.failed mode origin l t g node rule state
    let reached:=Listing8JumpEffects.finish mode origin failed (Listing8LoopControl.failureEnd mode origin l t g node rule state)
    StringStack.Trace mode (Listing8LoopControl.failureEnd mode origin l t g node rule state) (Listing8JumpLayout.forms mode origin failed) reached ∧
      reached.principal.pc=Arithmetic.encodeNat mode (Listing8JumpReturn.target mode origin failed) ∧
      MemoryRegion.Region.Contains ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ reached.principal.pc.toNat (Listing4TargetLayout.size mode) ∧
      MappedExecution.Window mode environment .execute reached.principal.pc.toNat (Listing4TargetLayout.size mode) ∧
      MappedExecution.Window mode environment .read reached.principal.pc.toNat (Listing4TargetLayout.size mode) :=
  Listing8JumpFetch.target_access mode environment origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) origin mapping _ _
    (Listing8LoopControl.entry mode origin l t g node rule ctx old state image)
    (placement mode origin g.transitions g.nodes _) ctx.native.capacity
    (Listing8LoopControl.current mode origin l t g node rule ctx old state image)

end SmcTuring.Appendix.Listing8LoopReturnFetch

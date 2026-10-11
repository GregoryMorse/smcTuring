module
public import SmcTuring.Appendix.Listing8JointAccumulatorCatalog

public section
namespace SmcTuring.Appendix.Listing8OriginalResetBinding
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev region:=Listing8LoopHaltImage.region
set_option maxHeartbeats 2000000

/-- The original reset packet is in the positively emitted image and remains
present at the actual bootstrap endpoint,whose full memory is restored. -/
theorem reset (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8ResetPackets.Initial mode (region mode origin l g)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.memory := by
  let r := region mode origin l g
  let failure := Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have tableBefore : Listing8FullTableImage.start mode origin≤r.start := by
    change Listing8FullTableImage.start mode origin≤Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)
    unfold Listing8TransitionTable.endPC;omega
  have order := Listing8GlobalControlLayout.ordered mode origin
  have callEq := Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode failure=Listing8JumpLayout.callPC mode origin at callEq
  have coords := Listing8FailureLayout.positions mode failure
  have after : failure.start≤r.start := by
    have callLower : failure.start≤Listing8FailureLayout.callPC mode failure := by
      dsimp only [Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,Listing8FailureLayout.xorPC,
        Listing8FailureLayout.andPC,Listing8FailureLayout.storePC,Listing8FailureLayout.notPC,
        Listing8FailureLayout.comparisonPC,Listing8FailureLayout.ownerPC];omega
    omega
  have nodeOutside : r.start+(Listing8ResetLayout.bytes mode r).length≤l.sourceNode := by
    rw [Listing8ResetLayout.bytes_length,←(Listing8ResetLayout.positions mode r).2.2.2]
    exact (reset_bounds mode origin l t g node rule ctx).nodeAfter
  have sourceOutside : l.sourceTransition+Listing8Prototypes.transitionSpan mode≤r.start := by
    rw [ctx.ruleLocated]
    have resetEq : r.start=Listing8GraphLayout.reset mode origin g.transitions := by
      change Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)=_
      rw [Listing8TransitionTable.endPC,table_length];rfl
    rw [resetEq]
    exact Listing8GraphLayout.transition_upper mode origin g.transitions rule.val rule.isLt
  rw [Listing8ResetPackets.Initial,
    Listing8OriginalControlImage.memory mode origin l t g node rule ctx memory seed,
    Listing8LoopOriginalImage.initial_memory mode origin l t g node rule ctx memory seed,initialMemory,
    Listing8LateFrames.initial_image mode l t _ _ _ ctx.resources ctx.body _ _ _ after (Or.inr nodeOutside) (Or.inl sourceOutside)]
  rw [Listing8FailureGlobalImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing8FailureGlobalImage.region_end]
    change Listing8FailureLayout.endPC mode failure≤r.start
    have endBefore : Listing8FailureLayout.endPC mode failure≤Listing8FailureLayout.callPC mode failure := by
      unfold Listing8FailureLayout.callPC;omega
    omega)),byte_frame _ _ _ _ _ (Or.inl (by
      change Listing8FailureLayout.callPC mode failure+(Native.encode mode (.callRelative (Listing8FailureLayout.original mode failure))).length≤r.start
      rw [Native.instruction_length]
      change Listing8FailureLayout.callPC mode failure+5≤r.start
      omega))]
  rw [extra,Listing8GlobalBoot.extra,byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing4EntryLayout.bytes_length]
    change Listing4EntryLayout.mainPC mode origin≤r.start
    omega)),Listing8JumpImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
      rw [Listing8JumpLayout.prefix_length]
      change Listing8JumpLayout.callPC mode origin≤r.start
      omega)),Listing8FailImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
      rw [Listing8FailLayout.bytes_length]
      exact tableBefore)),Listing8FullTableImage.backing,Listing8TransitionTable.image,
    byte_frame _ _ _ _ _ (Or.inl (by
      rw [Listing8TransitionTable.endpoint]
      exact le_refl _))]
  exact ByteMemory.bytes_at_put _ _ _

/-- Full original first-main entry,including the reset bytes needed for either
future logical branch,derived solely from present emission and execution. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopHaltImage.Current mode origin l t g node rule Listing8OriginalControlImage.old
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) :=
  ⟨Listing8OriginalControlImage.current mode origin l t g node rule ctx memory seed,
    reset mode origin l t g node rule ctx memory seed⟩

end SmcTuring.Appendix.Listing8OriginalResetBinding

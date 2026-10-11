module
public import SmcTuring.Appendix.Listing8PackedContext

public section
namespace SmcTuring.Appendix.Listing9PackedCapacity
open Native Listing8SourceGraph

/-- Exact total byte extent, including entry, all rules/nodes, epilogue and
both trailing declarations. The source counts are arbitrary naturals. -/
theorem endPC_exact (mode : Mode) (start transitions nodes : Nat) :
    Listing9PackedLayout.endPC mode start transitions nodes=
      start+(if mode=.x86 then 943 else 1481)+transitions*(if mode=.x86 then 66 else 84)+nodes*(if mode=.x86 then 46 else 64) := by
  unfold Listing9PackedLayout.endPC Listing9PackedLayout.pointerOwner Listing9PackedLayout.saveOwner Listing9PackedLayout.epilogue
  unfold Listing8GraphLayout.endPC Listing8GraphLayout.node Listing8GraphLayout.input Listing8GraphLayout.reset Listing8GraphLayout.transition
  rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset]
  cases mode <;> simp [Listing9PackedLayout.origin,AccumulatorLayout.storeSize,AccumulatorLayout.exchangeSize,
    instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,StringCodec.initialSize,Listing8Prototypes.transitionSpan,
    Listing8Prototypes.nodeSpan,Listing8Prototypes.pointerSpan,ReaderImage.totalSize,Nat.add_assoc] <;> omega

theorem bounds (mode : Mode) (start transitions nodes : Nat)
    (capacity : start+(if mode=.x86 then 943 else 1481)+transitions*(if mode=.x86 then 66 else 84)+nodes*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (reach : mode=.x64 → 1474+transitions*84+nodes*64≤2^31) :
    Listing9PackedLayout.Bounds mode start transitions nodes := by
  refine ⟨by rw [endPC_exact];exact capacity,?_⟩
  intro long
  subst mode
  have fit:=reach rfl
  rw [endPC_exact]
  simp only [reduceCtorEq,ite_false,Listing9PackedLayout.origin,AccumulatorLayout.storeSize]
  omega

theorem graph_bounds (mode : Mode) (start : Nat) (g : Graph)
    (bounds : Listing9PackedLayout.Bounds mode start g.transitions g.nodes) :
    Listing8GraphPointers.Bounds mode (Listing9PackedLayout.origin mode start) g := by
  have before : Listing8GraphLayout.endPC mode (Listing9PackedLayout.origin mode start) g.transitions g.nodes≤
      Listing9PackedLayout.endPC mode start g.transitions g.nodes := by
    dsimp [Listing9PackedLayout.endPC,Listing9PackedLayout.pointerOwner,Listing9PackedLayout.saveOwner,Listing9PackedLayout.epilogue]
    omega
  refine ⟨Nat.lt_of_le_of_lt before bounds.capacity,?_⟩
  intro long
  exact Nat.le_trans (Listing8GraphLayout.node_lower mode (Listing9PackedLayout.origin mode start) g.transitions g.nodes)
    (Nat.le_trans before (bounds.reach long))

/-- All original helper labels and resources are constructed, and their
Context is positively proved from only total native capacity and RIP reach. -/
theorem context (mode : Mode) (start : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing9PackedLayout.Bounds mode start g.transitions g.nodes) :
    Listing8GraphInputContext.Context mode (Listing9PackedLayout.origin mode start)
      (Listing8PackedBodyLayout.layout mode (Listing9PackedLayout.origin mode start) g node rule)
      (Listing8PackedBodyLayout.targets mode (Listing9PackedLayout.origin mode start)) g node rule :=
  Listing8PackedContext.context mode _ g node rule (graph_bounds mode start g bounds)

end SmcTuring.Appendix.Listing9PackedCapacity

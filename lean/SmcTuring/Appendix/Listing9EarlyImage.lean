module
public import SmcTuring.Appendix.Listing8AccumulatorRestored

public section
namespace SmcTuring.Appendix.Listing9EarlyImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem overlay_window (sites : List ByteOverlay.Site) (memory : ByteMemory.Memory) (observed count : Nat)
    (before : ∀ site∈sites, observed+count≤site.pc) :
    ByteMemory.bytesAt (ByteOverlay.run sites memory) observed count=ByteMemory.bytesAt memory observed count := by
  induction sites generalizing memory with
  | nil => rfl
  | cons site rest ih =>
    rw [ByteOverlay.run,ih _ (fun later member => before later (List.Mem.tail _ member))]
    exact Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inr (before site (List.Mem.head _)))

theorem input_after_origin (mode : Mode) (origin transitions : Nat) :
    origin≤Listing8GraphLayout.input mode origin transitions := by
  have before:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin transitions) (Listing8GraphLayout.table_before_input mode origin transitions)
  rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset] at before
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at before <;> omega

theorem sites_after_origin (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    ∀ site∈Listing8BootImage.sites mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin), origin≤site.pc := by
  have mainAfter : origin≤l.start := by
    rw [ctx.boot.packed]
    dsimp [Listing4EntryLayout.mainPC]
    omega
  have codeEnd:=code_length mode l
  have beforeInput:=ctx.resources.inputAfter
  have input:=Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined
  have direction : (Listing8DirectionGeometry.region mode l).start=Listing8LiteralInput.endPC mode l.input := rfl
  have stateBefore:=Listing8FailureFrames.state_before mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have stateCoords:=Listing8StateGeometry.positions mode l t ctx.body.state
  have bodyCoords:=Listing8FailureGeometry.positions mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.body
  have beforeState : l.start≤(Listing8StateGeometry.region mode l).start := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at stateCoords <;> omega
  intro site member
  simp only [Listing8BootImage.sites,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change origin≤Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at bodyCoords <;> omega
  · exact Nat.le_trans mainAfter (Nat.le_trans beforeState stateBefore)
  · exact Nat.le_trans mainAfter beforeState
  · change origin≤(Listing8DirectionGeometry.region mode l).start
    rw [direction]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input <;> omega
  · change origin≤Listing8CopyImage.codeEnd mode l;omega
  · change origin≤l.input.start;omega
  · exact mainAfter
  · change origin≤l.sourceNode
    rw [ctx.nodeLocated]
    exact Nat.le_trans (input_after_origin mode origin g.transitions) (Listing8GraphLayout.node_lower mode origin g.transitions node.val)
  · change origin≤l.sourceTransition
    rw [ctx.ruleLocated]
    change origin≤Listing8GraphLayout.transition mode origin rule.val
    have lower:=Listing8GraphLayout.transition_lower mode origin rule.val
    rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset] at lower
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at lower <;> omega

/-- Every emitted original body packet is at or after its entry origin.
An earlier prologue window survives complete initialization byte-for-byte. -/
theorem initial_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (observed count : Nat) (before : observed+count≤origin) :
    ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory) observed count=ByteMemory.bytesAt memory observed count := by
  have input:=input_after_origin mode origin g.transitions
  have tableLower : origin≤Listing8FullTableImage.start mode origin := by
    rw [Listing8FullTableImage.start,Listing8FailLayout.end_offset]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
  have reset : origin≤(Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)).start := by
    change origin≤Listing8FullTableImage.start mode origin+(table mode origin g).length*Listing8Prototypes.transitionSpan mode
    omega
  rw [initialMemory,Listing8BootImage.memory_overlay,overlay_window _ _ observed count
    (fun site member => Nat.le_trans before (sites_after_origin mode origin l t g node rule ctx site member)),
    extra,Listing8GlobalBoot.extra,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inr before),
    Listing8JumpImage.backing,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inr (by dsimp [Listing8JumpLayout.jumpPC];omega)),
    Listing8FailImage.backing,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inr (by dsimp [Listing8JumpLayout.failPC,Listing8JumpLayout.callPC,Listing8JumpLayout.jumpPC];omega)),
    Listing8FullTableImage.backing,Listing8TransitionTable.image,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inr (Nat.le_trans before tableLower)),
    Listing8TableResetImage.backing,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inr (Nat.le_trans before reset)),
    Listing8GraphNodeImage.image,Listing8NodeTable.image,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inr (Nat.le_trans before input))]

end SmcTuring.Appendix.Listing9EarlyImage

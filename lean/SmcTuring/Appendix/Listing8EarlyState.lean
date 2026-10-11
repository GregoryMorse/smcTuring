module
public import SmcTuring.Appendix.Listing8EarlyStages
public import SmcTuring.Appendix.Listing8FailureGlobalValues

public section
namespace SmcTuring.Appendix.Listing8EarlyState
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
theorem state_start (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8StateGeometry.Bounds mode l t) :
    l.start ≤ (Listing8StateGeometry.region mode l).start := by
  have coords:=(Listing8StateGeometry.positions mode l t bounds).1
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
theorem state_helpers (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8StateGeometry.Bounds mode l t)
    (writer : DwordLayout.Layout) (member : writer∈Listing8StateLayout.helpers mode (Listing8StateGeometry.region mode l)) :
    l.start ≤ writer.destination := by
  have lower:=state_start mode l t bounds
  cases mode
  all_goals simp only [Listing8StateLayout.helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
    Listing8StateLayout.halves,Listing8PointerCopies.halfCount] at * <;> omega
theorem state_packets (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8StateGeometry.Bounds mode l t)
    (writer : DwordPackets.Site) (member : writer∈Listing8StateLayout.packets mode (Listing8StateGeometry.region mode l)) :
    l.start ≤ writer.target := by
  have lower:=state_start mode l t bounds
  have cursor:=Listing8EarlyGeometry.second_cursor mode l
  cases mode
  all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,
    Listing8StateLayout.updates,Listing8DirectionLayout.group,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Listing8StateLayout.updatePC,Listing8StateLayout.maskPC,Listing8StateLayout.newPC,
    Listing8StateLayout.halves,Listing8PointerCopies.halfCount] at * <;> omega
theorem state (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8StateGeometry.Bounds mode l t) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count ≤ l.start)
    (tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8GlobalState.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8StateImage.memory mode l t v extra) observed count := by
  rw [Listing8GlobalState.finish,Listing8StateTrace.window mode (Listing8StateGeometry.region mode l)
    (Listing8StateGeometry.local_bounds mode l t r bounds) _ (Listing8GlobalState.entry mode l t v r owners copies bounds extra seed)
    observed count (fun writer member => Or.inr (Nat.le_trans before (state_helpers mode l t bounds writer member)))
    (fun writer member => Or.inr (Nat.le_trans before (state_packets mode l t bounds writer member)))]
  exact Listing8EarlyStages.head mode l t v r owners copies bounds.head (Listing8StateImage.backing mode l extra) seed observed count before tape
theorem failure (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat) (r : Resources mode l)
    (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (bounds : Listing8FailureGeometry.Bounds mode l t sentinel begin) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count ≤ l.start)
    (tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6) :
    ByteMemory.bytesAt (Listing8GlobalFailure.finish mode l t v sentinel begin extra seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8FailureGlobalImage.memory mode l t v sentinel begin extra) observed count := by
  have mainBefore : l.start ≤ (Listing8FailureGeometry.region mode l sentinel begin).start := by
    have coords:=(Listing8FailureGeometry.positions mode l t sentinel begin bounds).1
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  rw [Listing8FailureGlobalValues.before_window mode l t v sentinel begin r owners copies bounds extra seed observed count (Nat.le_trans before mainBefore)]
  exact state mode l t v r owners copies bounds.state (Listing8FailureGlobalImage.backing mode l sentinel begin extra) seed observed count before tape
end SmcTuring.Appendix.Listing8EarlyState

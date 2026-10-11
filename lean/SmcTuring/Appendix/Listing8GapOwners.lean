module
public import SmcTuring.Appendix.Listing8MainGeometry

public section
namespace SmcTuring.Appendix.Listing8GapOwners
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets

theorem pointer_targets (mode : Mode) (l : Layout) (t : Targets) (copies : Listing8PointerCopies.Bounds mode l t)
    (joined : l.input.start=Listing8PointerCopies.endPC mode l)
    (writer : DwordLayout.Layout) (member : writer∈Listing8PointerCopies.layouts mode l t) : l.input.start≤writer.destination := by
  have state:=copies.targetsAfter t.state (by simp)
  have back:=copies.targetsAfter t.back (by simp)
  have forward:=copies.targetsAfter t.forward (by simp)
  rw [←joined] at state back forward
  cases mode
  all_goals simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only
  all_goals omega

theorem pointers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (bounds : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (joined : l.input.start=Listing8PointerCopies.endPC mode l) (extra : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (lower : codeEnd mode l≤observed) (upper : observed+count≤l.input.start) :
    ByteMemory.bytesAt (Listing8PointerImage.finish mode l t v extra seed).principal.memory observed count=
      ByteMemory.bytesAt (image mode l v (Listing8PointerImage.backing mode l t extra)) observed count := by
  have prior:=(Listing8CopiedOwners.result mode l v r bounds (Listing8PointerImage.backing mode l t extra) seed).1
  have cursor:=Listing8PointerCopies.cursor_before mode l
  rw [Listing8PointerImage.finish,Listing8PointerImage.ownerFinish,Listing8PointerCopies.window_frame mode l t copies _ prior observed count
    (Or.inl (Nat.le_trans cursor lower))
    (fun writer member => Or.inr (Nat.le_trans upper (pointer_targets mode l t copies joined writer member)))]
  exact Listing8PointerImage.prefix_window mode l v r bounds _ seed observed count lower upper

end SmcTuring.Appendix.Listing8GapOwners

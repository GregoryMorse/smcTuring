module
public import SmcTuring.Appendix.Listing8FullTable

public section
namespace SmcTuring.Appendix.Listing8TableResetImage
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def region (mode : Mode) (origin : Nat) (l : Layout) (sentinel : Nat) (table : List (Values mode)) : Listing8ResetLayout.Layout :=
  ⟨Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) table,
    Listing8JumpLayout.callPC mode origin,Listing8BootImage.beginPC mode origin,
    Listing8FailureLayout.source mode (Listing8BootControl.region mode origin l sentinel),l.input.cursor,
    (Listing8StateGeometry.region mode l).cursor,Listing8FullTableImage.start mode origin⟩
@[expose] def backing (mode : Mode) (origin : Nat) (l : Layout) (sentinel : Nat) (table : List (Values mode)) (memory : ByteMemory.Memory) :=
  ByteMemory.putBytes memory (region mode origin l sentinel table).start
    (Listing8ResetLayout.bytes mode (region mode origin l sentinel table))
structure Bounds (mode : Mode) (origin : Nat) (l : Layout) (sentinel : Nat) (table : List (Values mode)) : Prop where
  declarations : Listing8FullTableImage.Bounds mode origin l table
  reset : Listing8ResetLayout.Bounds mode (region mode origin l sentinel table)
  nodeAfter : Listing8ResetLayout.endPC mode (region mode origin l sentinel table)≤l.sourceNode

/-- Reset begins after the whole table and resets to its fixed first label,
independently of the selected source blueprint used by the preceding body. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Bounds mode origin l sentinel table) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8ResetPackets.Initial mode (region mode origin l sentinel table)
      (Listing8FullTable.finish mode origin l t v sentinel table (backing mode origin l sentinel table memory) seed).principal.memory := by
  have selectedSpan:=Listing8TransitionTable.fields_bounds mode (Listing8FullTableImage.start mode origin) table index v selected
  have tableBefore : Listing8FullTableImage.start mode origin≤(region mode origin l sentinel table).start := by
    dsimp [region,Listing8TransitionTable.endPC]
    omega
  have after : Listing8JumpLayout.failPC mode origin≤(region mode origin l sentinel table).start := by
    dsimp [Listing8FullTableImage.start,Listing8FailLayout.endPC] at tableBefore
    omega
  have sourceOutside : l.sourceTransition+transitionSpan mode≤(region mode origin l sentinel table).start := by
    rw [located]
    exact selectedSpan.2
  have nodeOutside : (region mode origin l sentinel table).start+
      (Listing8ResetLayout.bytes mode (region mode origin l sentinel table)).length≤l.sourceNode := by
    rw [Listing8ResetLayout.bytes_length]
    have endEq:=(Listing8ResetLayout.positions mode (region mode origin l sentinel table)).2.2.2
    rw [←endEq]
    exact bounds.nodeAfter
  rw [Listing8ResetPackets.Initial,
    (Listing8FullTable.result mode origin l t v sentinel table index selected located r owners copies boot body bounds.declarations _ seed).2.1,
    Listing8ResetImage.body_window mode origin l t v sentinel r owners copies boot body _ seed _ _ after (Or.inr nodeOutside) (Or.inl sourceOutside)]
  rw [Listing8FailImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing8FailLayout.bytes_length]
    exact tableBefore)),Listing8FullTableImage.backing,Listing8TransitionTable.image,
    byte_frame _ _ _ _ _ (Or.inl (by rw [Listing8TransitionTable.endpoint];exact Nat.le_refl _))]
  exact ByteMemory.bytes_at_put memory _ _

theorem endpoint_offset (mode : Mode) (origin : Nat) (l : Layout) (sentinel : Nat) (table : List (Values mode)) :
    Listing8ResetLayout.endPC mode (region mode origin l sentinel table)=
      origin+(if mode=.x86 then 901 else 1399)+table.length*transitionSpan mode := by
  rw [(Listing8ResetLayout.positions mode (region mode origin l sentinel table)).2.2.2]
  change Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) table+_=origin+_+_
  rw [Listing8FullTable.endpoint_offset]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
end SmcTuring.Appendix.Listing8TableResetImage

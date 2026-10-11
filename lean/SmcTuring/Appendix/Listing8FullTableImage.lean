module
public import SmcTuring.Appendix.Listing8TableImage

public section
namespace SmcTuring.Appendix.Listing8FullTableImage
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def start (mode : Mode) (origin : Nat) := Listing8FailLayout.endPC mode origin
@[expose] def backing (mode : Mode) (origin : Nat) (table : List (Values mode)) (memory : ByteMemory.Memory) :=
  Listing8TransitionTable.image mode (start mode origin) table memory
structure Bounds (mode : Mode) (origin : Nat) (l : Layout) (table : List (Values mode)) : Prop where
  valid : Listing8TransitionTable.Valid mode (start mode origin) table
  capacity : Listing8TransitionTable.endPC mode (start mode origin) table<2^(8*mode.wordBytes)
  nodeAfter : Listing8TransitionTable.endPC mode (start mode origin) table≤l.sourceNode

theorem fail_bounds (mode : Mode) (origin : Nat) (l : Layout) (table : List (Values mode)) (index : Nat) (v : Values mode)
    (selected : Listing8TransitionTable.Selected mode table index v) (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (start mode origin) index)
    (bounds : Bounds mode origin l table) : Listing8FailLayout.Bounds mode origin l (start mode origin) := by
  have coords:=Listing8TransitionTable.fields_bounds mode (start mode origin) table index v selected
  have tableEnd : start mode origin≤Listing8TransitionTable.endPC mode (start mode origin) table := by
    dsimp [Listing8TransitionTable.endPC]
    omega
  exact ⟨Nat.le_refl _,Nat.lt_of_le_of_lt tableEnd bounds.capacity,
    Or.inr (Nat.le_trans tableEnd bounds.nodeAfter),Or.inr (by rw [located];exact coords.1)⟩

theorem extra_current (mode : Mode) (origin : Nat) (table : List (Values mode)) (memory : ByteMemory.Memory) :
    Listing8TransitionTable.Initial mode (start mode origin) table
      (Listing8GlobalBoot.extra mode origin (Listing8JumpImage.backing mode origin
        (Listing8FailImage.backing mode origin (backing mode origin table memory)))) := by
  have bootBefore : origin+Listing4EntryLayout.size mode≤start mode origin := by
    rw [start,Listing8FailLayout.end_offset]
    cases mode <;> dsimp [Listing4EntryLayout.size] <;> omega
  have prefixBefore : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length≤start mode origin := by
    rw [Listing8JumpLayout.prefix_length]
    change Listing8JumpLayout.callPC mode origin≤Listing8FailLayout.endPC mode origin
    dsimp [Listing8FailLayout.endPC,Listing8JumpLayout.failPC]
    omega
  rw [Listing8TransitionTable.Initial,Listing8GlobalBoot.extra,byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing4EntryLayout.bytes_length]
    exact bootBefore)),Listing8JumpImage.backing,byte_frame _ _ _ _ _ (Or.inl prefixBefore),
    Listing8FailImage.backing,byte_frame _ _ _ _ _ (Or.inl (by rw [Listing8FailLayout.bytes_length];exact Nat.le_refl _))]
  exact Listing8TransitionTable.initial_image mode (start mode origin) table memory

/-- The entire original table survives body execution, including a selected
source blueprint at any declared index. Its overlay is proved to be an
identity on initialized bytes, rather than an assumed image equality. -/
theorem body_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Bounds mode origin l table) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8TransitionTable.Initial mode (start mode origin) table
      (Listing8GlobalJump.bodyEnd mode origin l t v sentinel (Listing8FailImage.backing mode origin (backing mode origin table memory)) seed).principal.memory := by
  have after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin))+5≤start mode origin := by
    change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l sentinel)+5≤start mode origin
    rw [Listing8JumpImage.call_position mode origin l t sentinel boot body]
    dsimp [start,Listing8FailLayout.endPC,Listing8JumpLayout.failPC]
    omega
  have tapeOutside : l.sourceNode+10≤start mode origin ∨
      start mode origin+(Listing8TransitionTable.bytes mode (start mode origin) table).length≤l.sourceNode+6 := by
    right
    rw [Listing8TransitionTable.endpoint]
    have afterNode:=bounds.nodeAfter
    omega
  rw [Listing8TransitionTable.Initial,Listing8GlobalJump.bodyEnd,Listing8GlobalBoot.finish,
    Listing8LateFrames.after_failure mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _ _ _ after tapeOutside]
  exact Listing8TableImage.current mode l t v sentinel (Listing8BootImage.beginPC mode origin) (start mode origin)
    table index selected located r body _ after (Or.inr bounds.nodeAfter) (extra_current mode origin table memory)

theorem after_fail (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Bounds mode origin l table) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8TransitionTable.Initial mode (start mode origin) table
      (Listing8FailReturn.finish mode origin l t v sentinel (backing mode origin table memory) seed).principal.memory := by
  rw [Listing8FailReturn.effect mode origin l t v sentinel r owners copies boot body]
  exact body_current mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed
end SmcTuring.Appendix.Listing8FullTableImage

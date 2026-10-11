module
public import SmcTuring.Appendix.Listing8FullTableResetValues

public section
namespace SmcTuring.Appendix.Listing8FullTableNodeFrames
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def bodyEnd (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalJump.bodyEnd mode origin l t v sentinel
    (Listing8FailImage.backing mode origin (Listing8FullTableImage.backing mode origin table
      (Listing8TableResetImage.backing mode origin l sentinel table memory))) seed

/-- Actual original table execution restores all memory, and the printed
reset writes only earlier CALL and cursor fields. Every later input window,
including the already updated symbol, is retained. -/
theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8TableResetImage.Bounds mode origin l sentinel table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat)
    (after : Listing8ResetLayout.endPC mode (Listing8TableResetImage.region mode origin l sentinel table)≤observed) :
    ByteMemory.bytesAt (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).principal.memory observed count=
      ByteMemory.bytesAt (bodyEnd mode origin l t v sentinel table memory seed).principal.memory observed count := by
  have lower : (Listing8TableResetImage.region mode origin l sentinel table).start≤observed := by
    have ending:=(Listing8ResetLayout.positions mode (Listing8TableResetImage.region mode origin l sentinel table)).2.2.2
    omega
  have call : Listing8JumpLayout.callPC mode origin+5≤observed := Nat.le_trans bounds.reset.callBefore lower
  have input : l.input.cursor+mode.wordBytes≤observed := Nat.le_trans bounds.reset.inputCursorBefore lower
  have transition : (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤observed := Nat.le_trans bounds.reset.transitionCursorBefore lower
  rw [Listing8FullTableReset.effect mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed,
    StackWindows.word_window _ _ _ _ _ _ (Or.inl transition),
    StackWindows.word_window _ _ _ _ _ _ (Or.inl input),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl (by omega)),Listing8FullTableReset.entryState,
    (Listing8FullTable.result mode origin l t v sentinel table index selected located r owners copies boot body bounds.declarations _ seed).2.1]
  rfl

theorem tape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8TableResetImage.Bounds mode origin l sentinel table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).principal.memory (l.sourceNode+6)=
      if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape := by
  have frame:=congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes))
    (window mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed
      (l.sourceNode+6) 4 (by have after:=bounds.nodeAfter;omega))
  change DwordCode.get (Listing8FullTableReset.finish mode origin l t v sentinel table memory seed).principal.memory (l.sourceNode+6)=
    DwordCode.get (bodyEnd mode origin l t v sentinel table memory seed).principal.memory (l.sourceNode+6) at frame
  rw [frame]
  exact Listing8GlobalBootValues.tape mode origin l t v sentinel r owners copies body _ seed
end SmcTuring.Appendix.Listing8FullTableNodeFrames

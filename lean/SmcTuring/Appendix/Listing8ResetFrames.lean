module
public import SmcTuring.Appendix.Listing8ResetRun
public import SmcTuring.Appendix.Listing8FailTransitionValues

public section
namespace SmcTuring.Appendix.Listing8ResetFrames
open Native Listing8CopyImage Listing8GlobalReset
abbrev Targets:=Listing8PointerCopies.Targets

/-- Reset writes only earlier CALL/cursor fields. Every window inside the
source input node, including its updated output symbol, is retained. -/
theorem node_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat)
    (lower : l.sourceNode≤observed) (upper : observed+count≤l.sourceNode+Listing8Prototypes.nodeSpan mode) :
    ByteMemory.bytesAt (finish mode origin l t v sentinel memory seed).principal.memory observed count=
      ByteMemory.bytesAt (entryState mode origin l t v sentinel memory seed).principal.memory observed count := by
  have coords:=Listing8ResetGeometry.positions mode origin l t sentinel boot body located
  have positions : l.start≤l.input.cursor ∧ l.start≤(Listing8StateGeometry.region mode l).cursor ∧
      l.start≤Listing8JumpLayout.callPC mode origin+1 ∧
      l.input.cursor+mode.wordBytes≤Listing8JumpLayout.failPC mode origin ∧
      (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤Listing8JumpLayout.failPC mode origin := by
    change (Listing8ResetImage.region mode origin l sentinel).start=origin+(if mode=.x86 then 903 else 1394) ∧
      Listing8JumpLayout.callPC mode origin=origin+(if mode=.x86 then 801 else 1269) ∧
      (Listing8ResetImage.region mode origin l sentinel).inputSource=origin+(if mode=.x86 then 712 else 1154) ∧
      l.input.cursor=origin+(if mode=.x86 then 58 else 116) ∧
      (Listing8StateGeometry.region mode l).cursor=origin+(if mode=.x86 then 129 else 230) ∧
      l.sourceTransition=origin+(if mode=.x86 then 837 else 1310) at coords
    rw [boot.packed]
    dsimp only [Listing8JumpLayout.failPC]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,Mode.wordBytes] at coords ⊢ <;>
      dsimp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size] <;> omega
  have outside (written size : Nat) (before : l.start≤written)
      (after : written+size≤Listing8JumpLayout.failPC mode origin) :
      written+size≤observed ∨ observed+count≤written := by
    rcases body.nodeOutside with early | late
    · exact Or.inr (by omega)
    · change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l sentinel)+5≤l.sourceNode at late
      rw [Listing8JumpImage.call_position mode origin l t sentinel boot body] at late
      change Listing8JumpLayout.failPC mode origin≤l.sourceNode at late
      exact Or.inl (by omega)
  rw [effect mode origin l t v sentinel r owners copies boot body located block bounds memory seed,
    StackWindows.word_window _ _ _ _ _ _ (outside _ _ positions.2.1 positions.2.2.2.2),
    StackWindows.word_window _ _ _ _ _ _ (outside _ _ positions.1 positions.2.2.2.1),
    DwordMixedImage.bytes_frame _ _ _ _ _ (outside _ _ positions.2.2.1 (by dsimp [Listing8JumpLayout.failPC];omega))]

theorem tape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (finish mode origin l t v sentinel memory seed).principal.memory (l.sourceNode+6)=
      if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape := by
  have current:=node_window mode origin l t v sentinel r owners copies boot body located block bounds memory seed
    (l.sourceNode+6) 4 (by omega) (by
      have large : 10≤Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
      omega)
  have retained : DwordCode.get (finish mode origin l t v sentinel memory seed).principal.memory (l.sourceNode+6)=
      DwordCode.get (entryState mode origin l t v sentinel memory seed).principal.memory (l.sourceNode+6) :=
    congrArg (fun bytes : List LittleEndian.Byte => BitVec.ofNat 32 (LittleEndian.pack bytes)) current
  exact retained.trans (Listing8FailTransitionValues.tape mode origin l t v sentinel r owners copies boot body located block
    (Listing8ResetImage.backing mode origin l sentinel memory) seed)
end SmcTuring.Appendix.Listing8ResetFrames

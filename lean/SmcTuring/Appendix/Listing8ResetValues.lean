module
public import SmcTuring.Appendix.Listing8GlobalReset

public section
namespace SmcTuring.Appendix.Listing8ResetValues
open Native Listing8CopyImage Listing8GlobalReset
abbrev Targets:=Listing8PointerCopies.Targets

theorem failure_condition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    failed mode origin l t v sentinel memory seed=
      decide ((if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next)=Arithmetic.encodeNat mode sentinel) :=
  Listing8BootControl.failure_condition mode origin l t v sentinel r owners copies body _ seed

theorem input_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode sentinel := by
  have intervals:=Listing8ResetGeometry.intervals mode origin _ (Listing8ResetGeometry.positions mode origin l t sentinel boot body located)
  have apart : l.input.cursor+mode.wordBytes≤(Listing8StateGeometry.region mode l).cursor := intervals.1
  rw [effect mode origin l t v sentinel r owners copies boot body located block bounds memory seed,
    MixedFrames.word_after_word mode _ _ _ _ (Or.inr apart),MixedMemory.get_put]

theorem transition_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode l.sourceTransition := by
  rw [effect mode origin l t v sentinel r owners copies boot body located block bounds memory seed,MixedMemory.get_put]

theorem call_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (finish mode origin l t v sentinel memory seed).principal.memory (Listing8JumpLayout.callPC mode origin) 5=
      Native.encode mode (.callRelative (Listing8FailureLayout.original mode (Listing8BootControl.region mode origin l sentinel))) := by
  have intervals:=Listing8ResetGeometry.intervals mode origin _ (Listing8ResetGeometry.positions mode origin l t sentinel boot body located)
  have positive : 0<mode.wordBytes := by cases mode <;> decide
  have before : l.input.cursor+mode.wordBytes≤Listing8JumpLayout.callPC mode origin ∧
      (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤Listing8JumpLayout.callPC mode origin := by
    change l.input.cursor+mode.wordBytes≤(Listing8StateGeometry.region mode l).cursor ∧
      (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤Listing8FailureLayout.source mode (Listing8BootControl.region mode origin l sentinel) ∧
      Listing8FailureLayout.source mode (Listing8BootControl.region mode origin l sentinel)+mode.wordBytes≤Listing8JumpLayout.callPC mode origin+1 ∧
      Listing8JumpLayout.callPC mode origin+5≤l.sourceTransition at intervals
    omega
  rw [effect mode origin l t v sentinel r owners copies boot body located block bounds memory seed,
    StackWindows.word_window _ _ _ _ _ _ (Or.inl before.2),
    StackWindows.word_window _ _ _ _ _ _ (Or.inl before.1),Listing8ResetGeometry.original mode origin l t sentinel boot body]
  have current:=Listing8GlobalJump.call_packet mode origin l t v sentinel r owners copies boot body
    (Listing8FailImage.backing mode origin (Listing8ResetImage.backing mode origin l sentinel memory)) seed
  have restored : (entryState mode origin l t v sentinel memory seed).principal.memory=
      (Listing8GlobalJump.bodyEnd mode origin l t v sentinel
        (Listing8FailImage.backing mode origin (Listing8ResetImage.backing mode origin l sentinel memory)) seed).principal.memory :=
    (Listing8FailTransition.result mode origin l t v sentinel r owners copies boot body located block _ seed).2.1
  rw [←restored] at current
  exact Listing8CallSelection.operand_current mode _ _ _ _ current

theorem accumulator (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel memory seed).principal.accumulator=
      StringInit.accumulator mode l.sourceTransition (entryState mode origin l t v sentinel memory seed) := by
  have entry : (entryState mode origin l t v sentinel memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8ResetImage.region mode origin l sentinel).start :=
    (Listing8FailTransition.result mode origin l t v sentinel r owners copies boot body located block _ seed).1
  have intervals:=Listing8ResetGeometry.intervals mode origin _ (Listing8ResetGeometry.positions mode origin l t sentinel boot body located)
  have positive : 0<mode.wordBytes := by cases mode <;> decide
  have before : l.input.cursor+mode.wordBytes≤l.sourceTransition ∧
      Listing8JumpLayout.callPC mode origin+5≤l.sourceTransition := by
    change l.input.cursor+mode.wordBytes≤(Listing8StateGeometry.region mode l).cursor ∧
      (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤Listing8FailureLayout.source mode (Listing8BootControl.region mode origin l sentinel) ∧
      Listing8FailureLayout.source mode (Listing8BootControl.region mode origin l sentinel)+mode.wordBytes≤Listing8JumpLayout.callPC mode origin+1 ∧
      Listing8JumpLayout.callPC mode origin+5≤l.sourceTransition at intervals
    omega
  have fits : l.sourceTransition<2^(8*mode.wordBytes) := by
    have cap:=bounds.reset.ttapeFits
    change l.sourceTransition+mode.wordBytes<_ at cap
    omega
  rw [effect mode origin l t v sentinel r owners copies boot body located block bounds memory seed,
    Listing8ResetEffects.input_effect mode (Listing8ResetImage.region mode origin l sentinel) bounds.reset _ entry]
  cases mode with
  | x86 => rfl
  | x64 =>
    change Execution.load .x64 (ByteMemory.putWord .x64
      (DwordCode.put (entryState .x64 origin l t v sentinel memory seed).principal.memory
        (Listing8JumpLayout.callPC .x64 origin+1) (Listing8ResetLayout.original (Listing8ResetImage.region .x64 origin l sentinel)))
      l.input.cursor _) (Arithmetic.encodeNat .x64 l.sourceTransition)=_
    rw [MixedMemory.load_nat .x64 _ _ fits,MixedFrames.word_after_word .x64 _ _ _ _ (Or.inl before.1),
      MixedFrames.word_after_dword .x64 _ _ _ _ (Or.inl (by omega)),←MixedMemory.load_nat .x64 _ _ fits]
    rfl

theorem reset_reusable (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8ResetPackets.Initial mode (Listing8ResetImage.region mode origin l sentinel)
      (finish mode origin l t v sentinel memory seed).principal.memory := by
  have transitionBefore : (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤
      (Listing8ResetImage.region mode origin l sentinel).start := bounds.reset.transitionCursorBefore
  have inputBefore : l.input.cursor+mode.wordBytes≤(Listing8ResetImage.region mode origin l sentinel).start :=
    bounds.reset.inputCursorBefore
  have callBefore : Listing8JumpLayout.callPC mode origin+5≤(Listing8ResetImage.region mode origin l sentinel).start :=
    bounds.reset.callBefore
  rw [Listing8ResetPackets.Initial,effect mode origin l t v sentinel r owners copies boot body located block bounds memory seed,
    StackWindows.word_window _ _ _ _ _ _ (Or.inl transitionBefore),
    StackWindows.word_window _ _ _ _ _ _ (Or.inl inputBefore),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl (by omega))]
  exact Listing8ResetImage.current mode origin l t v sentinel r owners copies boot body located block bounds memory seed

theorem terminal_boundary (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Listing8ResetImage.Bounds mode origin l sentinel)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel memory seed).principal.pc.toNat=origin+(if mode=.x86 then 967 else 1483) := by
  rw [effect mode origin l t v sentinel r owners copies boot body located block bounds memory seed,
    Arithmetic.encode_nat_toNat mode _ bounds.reset.capacity,Listing8ResetImage.endpoint_offset mode origin l sentinel located]
end SmcTuring.Appendix.Listing8ResetValues

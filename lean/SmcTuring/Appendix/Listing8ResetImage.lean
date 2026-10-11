module
public import SmcTuring.Appendix.Listing8ResetTrace
public import SmcTuring.Appendix.Listing8RetainedInputSource

public section
namespace SmcTuring.Appendix.Listing8ResetImage
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def region (mode : Mode) (origin : Nat) (l : Layout) (sentinel : Nat) : Listing8ResetLayout.Layout :=
  ⟨l.sourceTransition+transitionSpan mode,Listing8JumpLayout.callPC mode origin,Listing8BootImage.beginPC mode origin,
    Listing8FailureLayout.source mode (Listing8BootControl.region mode origin l sentinel),l.input.cursor,
    (Listing8StateGeometry.region mode l).cursor,l.sourceTransition⟩
@[expose] def backing (mode : Mode) (origin : Nat) (l : Layout) (sentinel : Nat) (memory : ByteMemory.Memory) :=
  ByteMemory.putBytes memory (region mode origin l sentinel).start (Listing8ResetLayout.bytes mode (region mode origin l sentinel))

structure Bounds (mode : Mode) (origin : Nat) (l : Layout) (sentinel : Nat) : Prop where
  reset : Listing8ResetLayout.Bounds mode (region mode origin l sentinel)
  nodeOutside : l.sourceNode+nodeSpan mode≤(region mode origin l sentinel).start ∨
    Listing8ResetLayout.endPC mode (region mode origin l sentinel)≤l.sourceNode

/-- Later windows use per-window source separation, allowing the actual
inline transition blueprint to be the ttape code immediately before reset. -/
theorem body_window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat)
    (after : Listing8JumpLayout.failPC mode origin≤observed)
    (nodeOutside : l.sourceNode+nodeSpan mode≤observed ∨ observed+count≤l.sourceNode)
    (transitionOutside : l.sourceTransition+transitionSpan mode≤observed ∨ observed+count≤l.sourceTransition) :
    ByteMemory.bytesAt (Listing8GlobalJump.bodyEnd mode origin l t v sentinel memory seed).principal.memory observed count=
      ByteMemory.bytesAt memory observed count := by
  have large : 10≤nodeSpan mode := by cases mode <;> decide
  have tapeOutside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6 := by
    rcases nodeOutside with early | late
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have afterCall : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin))+5≤observed := by
    change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l sentinel)+5≤observed
    rw [Listing8JumpImage.call_position mode origin l t sentinel boot body]
    exact after
  have coords:=Listing8FailureLayout.positions mode (Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin))
  have afterRegion : (Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin)).start≤observed := by
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have bootBefore : origin+Listing4EntryLayout.size mode≤observed := by
    have location:=(Listing8JumpLayout.positions mode origin).2
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at location <;> dsimp [Listing4EntryLayout.size] <;> omega
  have prefixBefore : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length≤observed := by
    rw [Listing8JumpLayout.prefix_length]
    change Listing8JumpLayout.callPC mode origin≤observed
    dsimp [Listing8JumpLayout.failPC] at after
    omega
  rw [Listing8GlobalJump.bodyEnd,Listing8GlobalBoot.finish,
    Listing8LateFrames.after_failure mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _ observed count afterCall tapeOutside,
    Listing8LateFrames.initial_image mode l t v sentinel (Listing8BootImage.beginPC mode origin) r body _ observed count afterRegion nodeOutside transitionOutside]
  rw [Listing8FailureGlobalImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing8FailureGlobalImage.region_end]
    dsimp only [Listing8FailureLayout.callPC] at afterCall
    omega)),byte_frame _ _ _ _ _ (Or.inl afterCall)]
  rw [Listing8GlobalBoot.extra,byte_frame _ _ _ _ _ (Or.inl (by rw [Listing4EntryLayout.bytes_length];exact bootBefore)),
    Listing8JumpImage.backing,byte_frame _ _ _ _ _ (Or.inl prefixBefore)]

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (block : Listing8TransitionBlock.Bounds mode l.sourceTransition v)
    (bounds : Bounds mode origin l sentinel) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8ResetPackets.Initial mode (region mode origin l sentinel)
      (Listing8FailTransition.finish mode origin l t v sentinel (backing mode origin l sentinel memory) seed).principal.memory := by
  have lower : Listing8JumpLayout.failPC mode origin≤(region mode origin l sentinel).start := by
    change Listing8JumpLayout.failPC mode origin≤l.sourceTransition+transitionSpan mode
    rw [located]
    dsimp [Listing8FailLayout.endPC]
    omega
  have nodeOutside : l.sourceNode+nodeSpan mode≤(region mode origin l sentinel).start ∨
      (region mode origin l sentinel).start+(Listing8ResetLayout.bytes mode (region mode origin l sentinel)).length≤l.sourceNode := by
    have endpoint : (region mode origin l sentinel).start+(Listing8ResetLayout.bytes mode (region mode origin l sentinel)).length=
        Listing8ResetLayout.endPC mode (region mode origin l sentinel) := by
      rw [Listing8ResetLayout.bytes_length,(Listing8ResetLayout.positions mode (region mode origin l sentinel)).2.2.2]
    rw [endpoint]
    exact bounds.nodeOutside
  rw [Listing8ResetPackets.Initial,
    (Listing8FailTransition.result mode origin l t v sentinel r owners copies boot body located block _ seed).2.1,
    body_window mode origin l t v sentinel r owners copies boot body _ seed _ _ lower nodeOutside (Or.inl (Nat.le_refl _))]
  rw [Listing8FailImage.backing,byte_frame _ _ _ _ _ (Or.inl (by
    rw [Listing8FailLayout.bytes_length]
    change Listing8FailLayout.endPC mode origin≤(region mode origin l sentinel).start
    rw [←located]
    dsimp [region]
    omega))]
  exact ByteMemory.bytes_at_put memory _ _

theorem endpoint_offset (mode : Mode) (origin : Nat) (l : Layout) (sentinel : Nat)
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin) :
    Listing8ResetLayout.endPC mode (region mode origin l sentinel)=origin+(if mode=.x86 then 967 else 1483) := by
  rw [(Listing8ResetLayout.positions mode (region mode origin l sentinel)).2.2.2]
  change l.sourceTransition+transitionSpan mode+_=origin+_
  rw [Listing8FailTransition.endpoint_offset mode origin l located]
  cases mode <;> rfl
end SmcTuring.Appendix.Listing8ResetImage

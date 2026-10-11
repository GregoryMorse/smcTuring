module
public import SmcTuring.Appendix.Listing8ResetImage

public section
namespace SmcTuring.Appendix.Listing8ResetGeometry
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def Positions (mode : Mode) (origin : Nat) (fragment : Listing8ResetLayout.Layout) : Prop :=
  fragment.start=origin+(if mode=.x86 then 903 else 1394) ∧
  fragment.callPC=origin+(if mode=.x86 then 801 else 1269) ∧
  fragment.inputSource=origin+(if mode=.x86 then 712 else 1154) ∧
  fragment.inputCursor=origin+(if mode=.x86 then 58 else 116) ∧
  fragment.transitionCursor=origin+(if mode=.x86 then 129 else 230) ∧
  fragment.ttape=origin+(if mode=.x86 then 837 else 1310)

theorem positions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin) :
    Positions mode origin (Listing8ResetImage.region mode origin l sentinel) := by
  have failure:=Listing8FailureGeometry.positions mode l t sentinel (Listing8BootImage.beginPC mode origin) body
  have input:=Listing8InputBounds.positions mode l t body.state.head.input.fields body.state.head.input.joined
  have second:=(Listing8Initializer.code_geometry mode l).1
  refine ⟨Listing8FailTransition.endpoint_offset mode origin l located,
    (Listing8JumpLayout.positions mode origin).1,?_,?_,?_,?_⟩
  · change (Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin)).start+10+StringCodec.fieldOffset mode=_
    rw [failure.1,boot.packed]
    cases mode <;> rfl
  · change l.input.cursor=_
    rw [input.2.2,boot.packed]
    cases mode <;> rfl
  · change StringCodec.sourceField mode (secondStart mode l)=_
    rw [second,boot.packed]
    cases mode <;> rfl
  · change l.sourceTransition=_
    rw [located,Listing8FailLayout.end_offset]

/-- All reset reach, capacity and word/code separation certificates follow
from its derived packed positions and one end-of-tail native capacity bound. -/
theorem from_positions (mode : Mode) (origin : Nat) (fragment : Listing8ResetLayout.Layout)
    (coords : Positions mode origin fragment)
    (capacity : Listing8ResetLayout.endPC mode fragment<2^(8*mode.wordBytes)) :
    Listing8ResetLayout.Bounds mode fragment := by
  cases mode
  all_goals simp only [Positions,reduceCtorEq,ite_true,ite_false] at coords
  all_goals rcases coords with ⟨start,call,inputSource,inputCursor,transitionCursor,ttape⟩
  all_goals refine ⟨capacity,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try apply ConversionLayout.Admissible.mk
  all_goals try (intro only;cases only)
  all_goals simp only [Listing8ResetLayout.endPC,Listing8ResetLayout.markerPC,Listing8ResetLayout.transitionCopy,
    Listing8ResetLayout.ownerPC,Listing8ResetLayout.inputCopy,ConversionLayout.endPC,ConversionLayout.thirdPC,
    ConversionLayout.secondPC,ConversionLayout.exchangeSize,ConversionLayout.storeSize,StringInit.field,
    StringCodec.initialSize,StringCodec.fieldOffset,Native.instructionLength,MemoryOp.prefix,MemoryOp.trailer,
    wordPrefix,Mode.wordBytes,Relocation.SignedDelta,Relocation.delta,reduceCtorEq,ite_true,ite_false,
    List.length_nil,List.length_cons] at capacity ⊢
  all_goals simp only [start,call,inputSource,inputCursor,transitionCursor,ttape] at capacity ⊢
  all_goals omega

theorem intervals (mode : Mode) (origin : Nat) (fragment : Listing8ResetLayout.Layout)
    (coords : Positions mode origin fragment) :
    fragment.inputCursor+mode.wordBytes≤fragment.transitionCursor ∧
    fragment.transitionCursor+mode.wordBytes≤fragment.inputSource ∧
    fragment.inputSource+mode.wordBytes≤fragment.callPC+1 ∧
    fragment.callPC+5≤fragment.ttape := by
  cases mode <;> simp only [Positions,reduceCtorEq,ite_true,ite_false,Mode.wordBytes] at coords ⊢ <;>
    rcases coords with ⟨start,call,inputSource,inputCursor,transitionCursor,ttape⟩ <;> omega

theorem reset_bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (located : l.sourceTransition=Listing8FailLayout.endPC mode origin)
    (capacity : Listing8ResetLayout.endPC mode (Listing8ResetImage.region mode origin l sentinel)<2^(8*mode.wordBytes)) :
    Listing8ResetLayout.Bounds mode (Listing8ResetImage.region mode origin l sentinel) :=
  from_positions mode origin _ (positions mode origin l t sentinel boot body located) capacity

theorem original (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin)) :
    Listing8ResetLayout.original (Listing8ResetImage.region mode origin l sentinel)=
      Listing8FailureLayout.original mode (Listing8BootControl.region mode origin l sentinel) := by
  change Relocation.relative32 (Listing8JumpLayout.callPC mode origin+5) (Listing8BootImage.beginPC mode origin)=_
  rw [←Listing8JumpImage.call_position mode origin l t sentinel boot body]
  rfl
end SmcTuring.Appendix.Listing8ResetGeometry

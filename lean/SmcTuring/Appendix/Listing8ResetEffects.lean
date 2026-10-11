module
public import SmcTuring.Appendix.Listing8ResetPackets
public import SmcTuring.Native.MixedFrames

public section
namespace SmcTuring.Appendix.Listing8ResetEffects
open Native Listing8ResetLayout
@[expose] def afterStore (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringDword.execute mode (StringDword.store mode (storeDisp mode l) (original l)) state
@[expose] def afterInput (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringDwordCopy.wordFinish mode (inputCopy mode l) (afterStore mode l state)
@[expose] def afterOwner (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringExecution.run mode (StringInit.forms mode (ownerPC mode l) l.ttape) (afterInput mode l state)
@[expose] def afterTransition (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringDwordCopy.wordFinish mode (transitionCopy mode l) (afterOwner mode l state)
@[expose] def finish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  Listing8OriginalOwners.advance mode (marker mode l) (afterTransition mode l state)

theorem store_effect (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) :
    afterStore mode l state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (inputCopy mode l).start
      memory:=DwordCode.put state.principal.memory (l.callPC+1) (original l)}} := by
  have fits : l.callPC+1<2^(8*mode.wordBytes) := by have cap:=bounds.callFits;omega
  have effect:=DwordArithmetic.located_effect mode (.store 0 (original l)) l.start (l.callPC+1)
    state.principal rfl entry bounds.storeRange fits
  change DwordArithmetic.execute mode (.store (storeDisp mode l) (original l)) state.principal=
    {state.principal with pc:=Arithmetic.encodeNat mode (l.start+10),memory:=DwordCode.put state.principal.memory (l.callPC+1) (original l)} at effect
  rw [afterStore,StringDword.store_execute,effect]
  rfl

theorem input_effect (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) :
    afterInput mode l state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (ownerPC mode l)
      memory:=ByteMemory.putWord mode (DwordCode.put state.principal.memory (l.callPC+1) (original l))
        l.inputCursor (MixedMemory.getWord mode state.principal.memory l.inputSource)}} := by
  have location : (afterStore mode l state).principal.pc=Arithmetic.encodeNat mode (inputCopy mode l).start := by
    rw [store_effect mode l bounds state entry]
  rw [afterInput,WordCopyPacket.effect mode (inputCopy mode l) bounds.inputValid _ location,
    store_effect mode l bounds state entry]
  change {state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (ownerPC mode l)
      memory:=ByteMemory.putWord mode (DwordCode.put state.principal.memory (l.callPC+1) (original l)) l.inputCursor
        (MixedMemory.getWord mode (DwordCode.put state.principal.memory (l.callPC+1) (original l)) l.inputSource)}}=_
  rw [MixedFrames.word_after_dword mode _ _ _ _ (Or.inr bounds.inputSourceBeforeCall)]

theorem input_window (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (observed count : Nat)
    (after : l.start≤observed) :
    ByteMemory.bytesAt (afterInput mode l state).principal.memory observed count=
      ByteMemory.bytesAt state.principal.memory observed count := by
  rw [input_effect mode l bounds state entry,StackWindows.word_window _ _ _ _ _ _
    (Or.inl (Nat.le_trans bounds.inputCursorBefore after)),DwordMixedImage.bytes_frame _ _ _ _ _
    (Or.inl (by have before:=bounds.callBefore;omega))]

theorem owner_current (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (initial : Listing8ResetPackets.Initial mode l state.principal.memory) :
    ByteMemory.bytesAt (afterInput mode l state).principal.memory (ownerPC mode l) (StringCodec.initialSize mode)=
      StringInit.bytes mode (ownerPC mode l) l.ttape := by
  rw [input_window mode l bounds state entry _ _ (by
    have coords:=positions mode l
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega)]
  exact Listing8ResetPackets.owner_current mode l _ initial

theorem owner_effect (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (initial : Listing8ResetPackets.Initial mode l state.principal.memory) :
    afterOwner mode l state={afterInput mode l state with principal:={(afterInput mode l state).principal with
      pc:=Arithmetic.encodeNat mode (transitionCopy mode l).start
      accumulator:=StringInit.accumulator mode l.ttape (afterInput mode l state)}} := by
  have location : (afterInput mode l state).principal.pc=Arithmetic.encodeNat mode (ownerPC mode l) := by
    rw [input_effect mode l bounds state entry]
  exact StringInit.effect mode (ownerPC mode l) l.ttape _ location (owner_capacity mode l bounds)
    (owner_current mode l bounds state entry initial)

theorem owner_value (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (initial : Listing8ResetPackets.Initial mode l state.principal.memory) :
    MixedMemory.getWord mode (afterOwner mode l state).principal.memory (transitionCopy mode l).source=
      Arithmetic.encodeNat mode l.ttape := by
  have cap:=owner_capacity mode l bounds
  have fits : StringInit.field mode (ownerPC mode l)<2^(8*mode.wordBytes) := by
    cases mode <;> simp only [StringInit.field,StringCodec.fieldOffset,StringCodec.initialSize,Mode.wordBytes] at cap ⊢ <;> omega
  have value:=StringInit.initialized_pointer mode (ownerPC mode l) l.ttape _ cap
    (owner_current mode l bounds state entry initial)
  rw [MixedMemory.load_nat mode _ _ fits] at value
  rw [owner_effect mode l bounds state entry initial]
  exact value

theorem transition_effect (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (initial : Listing8ResetPackets.Initial mode l state.principal.memory) :
    afterTransition mode l state={afterOwner mode l state with principal:={(afterOwner mode l state).principal with
      pc:=Arithmetic.encodeNat mode (markerPC mode l)
      memory:=ByteMemory.putWord mode (afterOwner mode l state).principal.memory l.transitionCursor (Arithmetic.encodeNat mode l.ttape)}} := by
  have location : (afterOwner mode l state).principal.pc=Arithmetic.encodeNat mode (transitionCopy mode l).start := by
    rw [owner_effect mode l bounds state entry initial]
  rw [afterTransition,WordCopyPacket.effect mode (transitionCopy mode l) bounds.transitionValid _ location,
    owner_value mode l bounds state entry initial]
  rfl

theorem marker_current (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (initial : Listing8ResetPackets.Initial mode l state.principal.memory) :
    Listing8OriginalOwners.Current mode (marker mode l) (afterTransition mode l state).principal.memory := by
  change ByteMemory.bytesAt (afterTransition mode l state).principal.memory (markerPC mode l) 10=DwordOwner.bytes mode (markerPC mode l) 0
  rw [transition_effect mode l bounds state entry initial,owner_effect mode l bounds state entry initial]
  have after : l.start≤markerPC mode l := by
    have coords:=positions mode l
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  rw [StackWindows.word_window _ _ _ _ _ _ (Or.inl (Nat.le_trans bounds.transitionCursorBefore after)),
    input_window mode l bounds state entry _ _ after,←marker_bytes]
  exact Listing8ResetPackets.marker_current mode l _ initial

theorem effect (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (initial : Listing8ResetPackets.Initial mode l state.principal.memory) :
    finish mode l state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (endPC mode l)
      accumulator:=StringInit.accumulator mode l.ttape (afterInput mode l state)
      memory:=ByteMemory.putWord mode
        (ByteMemory.putWord mode (DwordCode.put state.principal.memory (l.callPC+1) (original l))
          l.inputCursor (MixedMemory.getWord mode state.principal.memory l.inputSource))
        l.transitionCursor (Arithmetic.encodeNat mode l.ttape)}} := by
  have location : (afterTransition mode l state).principal.pc=Arithmetic.encodeNat mode (markerPC mode l) := by
    rw [transition_effect mode l bounds state entry initial]
  rw [finish,Listing8OriginalOwners.advance_effect mode (marker mode l) _ (marker_capacity mode l bounds) location
    (marker_current mode l bounds state entry initial),transition_effect mode l bounds state entry initial,
    owner_effect mode l bounds state entry initial,input_effect mode l bounds state entry]
  rfl
end SmcTuring.Appendix.Listing8ResetEffects

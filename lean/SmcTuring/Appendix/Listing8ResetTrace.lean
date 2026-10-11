module
public import SmcTuring.Appendix.Listing8ResetEffects

public section
namespace SmcTuring.Appendix.Listing8ResetTrace
open Native Listing8ResetLayout Listing8ResetEffects

theorem store_window (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (observed count : Nat)
    (after : l.start≤observed) :
    ByteMemory.bytesAt (afterStore mode l state).principal.memory observed count=
      ByteMemory.bytesAt state.principal.memory observed count := by
  rw [store_effect mode l bounds state entry,DwordMixedImage.bytes_frame _ _ _ _ _
    (Or.inl (by have before:=bounds.callBefore;omega))]

/-- The entire printed reset and pure DOHALT marker execute from one complete
initial packet. Every later fetch is derived across preceding actual writes. -/
theorem trace (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (initial : Listing8ResetPackets.Initial mode l state.principal.memory) :
    StringDword.Trace mode state (program mode l) (finish mode l state) := by
  have coords:=positions mode l
  have fits : l.start<2^(8*mode.wordBytes) := by
    have cap:=bounds.capacity
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have first : StringDword.Trace mode state [StringDword.store mode (storeDisp mode l) (original l)] (afterStore mode l state) := by
    rw [afterStore,StringDword.store_execute]
    apply StringDword.store_trace
    rw [entry,Arithmetic.encode_nat_toNat mode _ fits]
    exact Listing8ResetPackets.store_current mode l _ initial
  have inputEntry : (afterStore mode l state).principal.pc=Arithmetic.encodeNat mode (inputCopy mode l).start := by
    rw [store_effect mode l bounds state entry]
  have inputPacket : ByteMemory.bytesAt (afterStore mode l state).principal.memory (inputCopy mode l).start
      (WordCopyPacket.bytes mode (inputCopy mode l)).length=WordCopyPacket.bytes mode (inputCopy mode l) := by
    rw [store_window mode l bounds state entry _ _ (by dsimp [inputCopy];omega)]
    exact Listing8ResetPackets.input_current mode l _ initial
  have second:=WordCopyPacket.trace mode (inputCopy mode l) bounds.inputValid _ inputEntry inputPacket
  have ownerEntry : (afterInput mode l state).principal.pc=Arithmetic.encodeNat mode (ownerPC mode l) := by
    rw [input_effect mode l bounds state entry]
  have third:=StringDword.string_trace mode (StringInitTrace.trace mode (ownerPC mode l) l.ttape _ ownerEntry
    (owner_capacity mode l bounds) bounds.ttapeFits bounds.ttapeOutside (owner_current mode l bounds state entry initial))
  have transitionEntry : (afterOwner mode l state).principal.pc=Arithmetic.encodeNat mode (transitionCopy mode l).start := by
    rw [owner_effect mode l bounds state entry initial]
  have transitionPacket : ByteMemory.bytesAt (afterOwner mode l state).principal.memory (transitionCopy mode l).start
      (WordCopyPacket.bytes mode (transitionCopy mode l)).length=WordCopyPacket.bytes mode (transitionCopy mode l) := by
    rw [owner_effect mode l bounds state entry initial,input_window mode l bounds state entry _ _ (by
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega)]
    exact Listing8ResetPackets.transition_current mode l _ initial
  have fourth:=WordCopyPacket.trace mode (transitionCopy mode l) bounds.transitionValid _ transitionEntry transitionPacket
  have markerEntry : (afterTransition mode l state).principal.pc=Arithmetic.encodeNat mode (Listing8OriginalOwners.pc mode (marker mode l)) := by
    rw [transition_effect mode l bounds state entry initial]
    rfl
  have last:=Listing8OriginalOwners.advance_trace mode (marker mode l) _ (marker_capacity mode l bounds)
    markerEntry (marker_current mode l bounds state entry initial)
  simpa only [program,finish,List.append_assoc] using StringDword.trace_append mode first (StringDword.trace_append mode second
    (StringDword.trace_append mode third (StringDword.trace_append mode fourth last)))
end SmcTuring.Appendix.Listing8ResetTrace

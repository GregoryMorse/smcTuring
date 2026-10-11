module
public import SmcTuring.Appendix.Listing8ResetTrace
public import SmcTuring.Appendix.Listing8OriginalOwnerWrites
public import SmcTuring.Native.StringCopyWrites
public import SmcTuring.Native.StringInitWrites

public section
namespace SmcTuring.Appendix.Listing8ResetWrites
open Native Listing8ResetLayout Listing8ResetEffects

structure Placement (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) : Prop where
  region : codeStart≤l.start ∧ endPC mode l≤codeEnd
  call : codeStart≤l.callPC+1 ∧ l.callPC+5≤codeEnd
  source : codeStart≤l.inputSource ∧ l.inputSource+mode.wordBytes≤codeEnd
  input : codeStart≤l.inputCursor ∧ l.inputCursor+mode.wordBytes≤codeEnd
  transition : codeStart≤l.transitionCursor ∧ l.transitionCursor+mode.wordBytes≤codeEnd
  ttape : codeStart≤l.ttape ∧ l.ttape+mode.wordBytes≤codeEnd

theorem owner_field (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (placed : Placement mode codeStart codeEnd l) :
    codeStart≤StringInit.field mode (ownerPC mode l) ∧ StringInit.field mode (ownerPC mode l)+mode.wordBytes≤codeEnd := by
  have coords:=positions mode l
  have inside:=placed.region
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;>
    simp [StringInit.field,StringCodec.fieldOffset,Mode.wordBytes] <;> omega

theorem marker_field (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (placed : Placement mode codeStart codeEnd l) :
    Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd (marker mode l) := by
  have inside:=placed.region
  change codeStart≤markerPC mode l+6 ∧ markerPC mode l+10≤codeEnd
  have coords:=positions mode l
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega

/-- The actual CALL-operand reset, word copies, DEFDATA and unchanged pure
marker stores have complete code-owned spans. Later states follow execution. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (bounds : Bounds mode l)
    (placed : Placement mode codeStart codeEnd l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (initial : Listing8ResetPackets.Initial mode l state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd ((program mode l).map (StringStoreWrites.liftDword mode)) state := by
  have coords:=positions mode l
  have storeFits : l.callPC+1<2^(8*mode.wordBytes) := by have cap:=bounds.callFits;omega
  have first:=StringStoreWrites.located mode codeStart codeEnd l.start (l.callPC+1) (original l) state entry
    bounds.storeRange storeFits (by have inside:=placed.call;omega)
  have inputEntry : (afterStore mode l state).principal.pc=Arithmetic.encodeNat mode (inputCopy mode l).start := by
    rw [store_effect mode l bounds state entry]
  have second:=StringCopyWrites.word mode codeStart codeEnd (inputCopy mode l) bounds.inputValid (afterStore mode l state)
    inputEntry placed.source placed.input
  have ownerEntry : (afterInput mode l state).principal.pc=Arithmetic.encodeNat mode (ownerPC mode l) := by
    rw [input_effect mode l bounds state entry]
  have third:=StringInitWrites.owned mode codeStart codeEnd (ownerPC mode l) l.ttape (afterInput mode l state)
    ownerEntry (owner_capacity mode l bounds) bounds.ttapeFits (owner_field mode codeStart codeEnd l placed) placed.ttape
    (owner_current mode l bounds state entry initial)
  have transitionEntry : (afterOwner mode l state).principal.pc=Arithmetic.encodeNat mode (transitionCopy mode l).start := by
    rw [owner_effect mode l bounds state entry initial]
  have fourth:=StringCopyWrites.word mode codeStart codeEnd (transitionCopy mode l) bounds.transitionValid (afterOwner mode l state)
    transitionEntry (owner_field mode codeStart codeEnd l placed) placed.transition
  have markerEntry : (afterTransition mode l state).principal.pc=Arithmetic.encodeNat mode (Listing8OriginalOwners.pc mode (marker mode l)) := by
    rw [transition_effect mode l bounds state entry initial];rfl
  have last:=Listing8OriginalOwnerWrites.advance_owned mode codeStart codeEnd (marker mode l)
    (marker_field mode codeStart codeEnd l placed) (afterTransition mode l state) (marker_capacity mode l bounds) markerEntry
    (marker_current mode l bounds state entry initial)
  have firstRun : StringWrites.run mode (([StringDword.store mode (storeDisp mode l) (original l)]).map (StringStoreWrites.liftDword mode)) state=
      afterStore mode l state := rfl
  have inputPacket : ByteMemory.bytesAt (afterStore mode l state).principal.memory (inputCopy mode l).start
      (WordCopyPacket.bytes mode (inputCopy mode l)).length=WordCopyPacket.bytes mode (inputCopy mode l) := by
    rw [Listing8ResetTrace.store_window mode l bounds state entry _ _ (by dsimp [inputCopy];omega)]
    exact Listing8ResetPackets.input_current mode l _ initial
  have secondRun:=StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (WordCopyPacket.trace mode (inputCopy mode l) bounds.inputValid (afterStore mode l state) inputEntry inputPacket))
  change StringWrites.run mode ((StringDwordCopy.wordProgram mode (inputCopy mode l)).map (StringStoreWrites.liftDword mode))
    (afterStore mode l state)=afterInput mode l state at secondRun
  have lifting : (fun form : StringForm.Form mode => StringStoreWrites.liftDword mode (StringDword.Form.string form))=StringWrites.liftString mode := by
    funext form;rfl
  have thirdRun : StringWrites.run mode (((StringInit.forms mode (ownerPC mode l) l.ttape).map StringDword.Form.string).map (StringStoreWrites.liftDword mode))
      (afterInput mode l state)=afterOwner mode l state := by
    rw [List.map_map];change StringWrites.run mode ((StringInit.forms mode (ownerPC mode l) l.ttape).map (StringWrites.liftString mode)) _=_
    exact StringWrites.run_lift_string mode _ _
  have transitionPacket : ByteMemory.bytesAt (afterOwner mode l state).principal.memory (transitionCopy mode l).start
      (WordCopyPacket.bytes mode (transitionCopy mode l)).length=WordCopyPacket.bytes mode (transitionCopy mode l) := by
    rw [owner_effect mode l bounds state entry initial,input_window mode l bounds state entry _ _ (by
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega)]
    exact Listing8ResetPackets.transition_current mode l _ initial
  have fourthRun:=StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (WordCopyPacket.trace mode (transitionCopy mode l) bounds.transitionValid (afterOwner mode l state) transitionEntry transitionPacket))
  change StringWrites.run mode ((StringDwordCopy.wordProgram mode (transitionCopy mode l)).map (StringStoreWrites.liftDword mode))
    (afterOwner mode l state)=afterTransition mode l state at fourthRun
  rw [program,List.map_append,List.map_append,List.map_append,List.map_append,
    StringWrites.owned_run_append,StringWrites.owned_run_append,StringWrites.owned_run_append,StringWrites.owned_run_append]
  simp only [StringWrites.run_append,firstRun,secondRun,thirdRun,fourthRun]
  refine ⟨⟨⟨⟨⟨first,trivial⟩,second⟩,?_⟩,fourth⟩,last⟩
  simpa only [List.map_map,Function.comp_def,lifting] using third

end SmcTuring.Appendix.Listing8ResetWrites

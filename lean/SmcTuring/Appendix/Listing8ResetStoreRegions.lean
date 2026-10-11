module
public import SmcTuring.Appendix.Listing8ResetWrites
public import SmcTuring.Native.WordCopyStoreRegions

public section
namespace SmcTuring.Appendix.Listing8ResetStoreRegions
open Native Listing8ResetLayout Listing8ResetEffects

@[expose] def fields (mode : Mode) (l : Layout) : List (Nat × Nat) :=
  [(l.callPC+1,4),(l.inputSource,mode.wordBytes),(l.inputCursor,mode.wordBytes),
    (StringInit.field mode (ownerPC mode l),mode.wordBytes),(l.ttape,mode.wordBytes),
    (l.transitionCursor,mode.wordBytes),(markerPC mode l+6,4)]
@[expose] def Allowed (mode : Mode) (l : Layout) (address count : Nat) : Prop := (address,count)∈fields mode l

theorem field_count (mode : Mode) (l : Layout) : (fields mode l).length=7 := rfl

/-- Every complete reset store is one of seven exact emitted operand windows;
all later entries and helper images are derived from actual execution. -/
theorem regions (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (initial : Listing8ResetPackets.Initial mode l state.principal.memory) :
    StringStoreRegions.Run mode (Allowed mode l) ((program mode l).map (StringStoreWrites.liftDword mode)) state := by
  have coords:=positions mode l
  have storeFits : l.callPC+1<2^(8*mode.wordBytes) := by have cap:=bounds.callFits;omega
  have firstOwned:=StringStoreWrites.located mode (l.callPC+1) (l.callPC+5) l.start (l.callPC+1) (original l) state entry
    bounds.storeRange storeFits ⟨Nat.le_refl _,by omega⟩
  have first:=BoundedStoreRegions.packet mode (Allowed mode l) (l.callPC+1) 4 _ state firstOwned
    (StringStoreWrites.length mode _ _ _) (by simp [Allowed,fields])
  have inputEntry : (afterStore mode l state).principal.pc=Arithmetic.encodeNat mode (inputCopy mode l).start := by
    rw [store_effect mode l bounds state entry]
  have second:=WordCopyStoreRegions.regions mode (Allowed mode l) (inputCopy mode l) bounds.inputValid (afterStore mode l state)
    inputEntry (by simp [Allowed,fields,inputCopy]) (by simp [Allowed,fields,inputCopy])
  have ownerEntry : (afterInput mode l state).principal.pc=Arithmetic.encodeNat mode (ownerPC mode l) := by
    rw [input_effect mode l bounds state entry]
  have third:=StringStoreTemplateRuns.initializer mode (Allowed mode l) (ownerPC mode l) l.ttape (afterInput mode l state)
    ownerEntry (owner_capacity mode l bounds) bounds.ttapeFits (owner_current mode l bounds state entry initial)
    (by simp [Allowed,fields]) (by simp [Allowed,fields])
  have transitionEntry : (afterOwner mode l state).principal.pc=Arithmetic.encodeNat mode (transitionCopy mode l).start := by
    rw [owner_effect mode l bounds state entry initial]
  have fourth:=WordCopyStoreRegions.regions mode (Allowed mode l) (transitionCopy mode l) bounds.transitionValid (afterOwner mode l state)
    transitionEntry (by simp [Allowed,fields,transitionCopy]) (by simp [Allowed,fields,transitionCopy])
  have markerEntry : (afterTransition mode l state).principal.pc=Arithmetic.encodeNat mode (Listing8OriginalOwners.pc mode (marker mode l)) := by
    rw [transition_effect mode l bounds state entry initial];rfl
  have markerFits : markerPC mode l+6<2^(8*mode.wordBytes) := by have cap:=bounds.capacity;dsimp [endPC] at cap;omega
  have lastOwned:=StringStoreWrites.located mode (markerPC mode l+6) (markerPC mode l+10) (markerPC mode l) (markerPC mode l+6) 0
    (afterTransition mode l state) markerEntry (fun _ => DwordOwner.reach _) markerFits ⟨Nat.le_refl _,by omega⟩
  have last : StringStoreRegions.Run mode (Allowed mode l)
      ((Listing8OriginalOwners.forms mode (marker mode l)).map (StringStoreWrites.liftDword mode)) (afterTransition mode l state) :=
    ⟨BoundedStoreRegions.packet mode (Allowed mode l) (markerPC mode l+6) 4 _ _ lastOwned
      (StringStoreWrites.length mode _ _ _) (by simp [Allowed,fields]),trivial⟩
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
    StringStoreRegions.append,StringStoreRegions.append,StringStoreRegions.append,StringStoreRegions.append]
  simp only [StringWrites.run_append,firstRun,secondRun,thirdRun,fourthRun]
  refine ⟨⟨⟨⟨⟨first,trivial⟩,second⟩,?_⟩,fourth⟩,last⟩
  simpa only [List.map_map,Function.comp_def,lifting] using third


end SmcTuring.Appendix.Listing8ResetStoreRegions

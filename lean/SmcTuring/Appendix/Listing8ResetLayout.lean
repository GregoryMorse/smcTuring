module
public import SmcTuring.Native.WordCopyPacket
public import SmcTuring.Native.StringInitTrace
public import SmcTuring.Native.TerminalMarker
public import SmcTuring.Appendix.Listing8OriginalOwners

public section
namespace SmcTuring.Appendix.Listing8ResetLayout
open Native

/-- Static addresses of the printed tail after the transition declarations. -/
structure Layout where
  start : Nat
  callPC : Nat
  beginPC : Nat
  inputSource : Nat
  inputCursor : Nat
  transitionCursor : Nat
  ttape : Nat

@[expose] def inputCopy (mode : Mode) (l : Layout) : ConversionLayout.Layout :=
  ⟨l.start+10,l.inputSource,l.inputCursor⟩
@[expose] def ownerPC (mode : Mode) (l : Layout) := ConversionLayout.endPC mode (inputCopy mode l)
@[expose] def transitionCopy (mode : Mode) (l : Layout) : ConversionLayout.Layout :=
  ⟨ownerPC mode l+StringCodec.initialSize mode,StringInit.field mode (ownerPC mode l),l.transitionCursor⟩
@[expose] def markerPC (mode : Mode) (l : Layout) := ConversionLayout.endPC mode (transitionCopy mode l)
@[expose] def endPC (mode : Mode) (l : Layout) := markerPC mode l+10
@[expose] def original (l : Layout) := Relocation.relative32 (l.callPC+5) l.beginPC
@[expose] def storeDisp (mode : Mode) (l : Layout) := Relocation.memoryDisp mode (l.start+10) (l.callPC+1)
@[expose] def store (mode : Mode) (l : Layout) : DwordArithmetic.Form := .store (storeDisp mode l) (original l)
@[expose] def marker (mode : Mode) (l : Layout) : Listing8OriginalOwners.Owner mode := .scalar (markerPC mode l) 0
@[expose] def bytes (mode : Mode) (l : Layout) :=
  DwordArithmetic.encode (store mode l)++WordCopyPacket.bytes mode (inputCopy mode l)++
    StringInit.bytes mode (ownerPC mode l) l.ttape++WordCopyPacket.bytes mode (transitionCopy mode l)++
    TerminalMarker.bytes mode (markerPC mode l)
@[expose] def program (mode : Mode) (l : Layout) :=
  [StringDword.store mode (storeDisp mode l) (original l)]++StringDwordCopy.wordProgram mode (inputCopy mode l)++
    (StringInit.forms mode (ownerPC mode l) l.ttape).map StringDword.Form.string++
    StringDwordCopy.wordProgram mode (transitionCopy mode l)++Listing8OriginalOwners.forms mode (marker mode l)

/-- All premises concern initial native capacity, relocation and static
interval separation. No later memory, value, fetch or trace is a premise. -/
structure Bounds (mode : Mode) (l : Layout) : Prop where
  capacity : endPC mode l<2^(8*mode.wordBytes)
  callFits : l.callPC+5≤2^(8*mode.wordBytes)
  callBefore : l.callPC+5≤l.start
  inputCursorBefore : l.inputCursor+mode.wordBytes≤l.start
  transitionCursorBefore : l.transitionCursor+mode.wordBytes≤l.start
  inputSourceBeforeCall : l.inputSource+mode.wordBytes≤l.callPC+1
  storeRange : mode=.x64 → Relocation.SignedDelta (l.start+10) (l.callPC+1)
  inputValid : ConversionLayout.Admissible mode (inputCopy mode l)
  transitionValid : ConversionLayout.Admissible mode (transitionCopy mode l)
  ttapeFits : l.ttape+mode.wordBytes<2^(8*mode.wordBytes)
  ttapeOutside : l.ttape+mode.wordBytes≤ownerPC mode l ∨ ownerPC mode l+StringCodec.initialSize mode≤l.ttape

theorem positions (mode : Mode) (l : Layout) :
    ownerPC mode l=l.start+(if mode=.x86 then 27 else 31) ∧
    (transitionCopy mode l).start=l.start+(if mode=.x86 then 37 else 58) ∧
    markerPC mode l=l.start+(if mode=.x86 then 54 else 79) ∧
    endPC mode l=l.start+(if mode=.x86 then 64 else 89) := by
  cases mode <;> simp [ownerPC,inputCopy,transitionCopy,markerPC,endPC,ConversionLayout.endPC,
    ConversionLayout.thirdPC,ConversionLayout.secondPC,ConversionLayout.exchangeSize,
    ConversionLayout.storeSize,StringCodec.initialSize,instructionLength,MemoryOp.prefix,
    MemoryOp.trailer,wordPrefix,Nat.add_assoc]

theorem bytes_length (mode : Mode) (l : Layout) : (bytes mode l).length=if mode=.x86 then 64 else 89 := by
  rw [bytes,List.length_append,List.length_append,List.length_append,List.length_append,
    DwordArithmetic.encode_length,WordCopyPacket.bytes_length,WordCopyPacket.bytes_length,
    TerminalMarker.length]
  have owner : (StringInit.bytes mode (ownerPC mode l) l.ttape).length=StringCodec.initialSize mode :=
    StringCodec.initial_length mode _ _ _
  rw [owner]
  cases mode <;> rfl

theorem instruction_count (mode : Mode) (l : Layout) : (program mode l).length=if mode=.x86 then 9 else 12 := by
  cases mode <;> rfl

theorem marker_bytes (mode : Mode) (l : Layout) :
    TerminalMarker.bytes mode (markerPC mode l)=DwordOwner.bytes mode (markerPC mode l) 0 := by
  cases mode <;> rfl

theorem owner_capacity (mode : Mode) (l : Layout) (bounds : Bounds mode l) :
    ownerPC mode l+StringCodec.initialSize mode<2^(8*mode.wordBytes) := by
  have cap:=bounds.capacity
  have coords:=positions mode l
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords cap ⊢ <;>
    dsimp [StringCodec.initialSize] <;> omega

theorem marker_capacity (mode : Mode) (l : Layout) (bounds : Bounds mode l) :
    Listing8OriginalOwners.Valid mode (marker mode l) := bounds.capacity
end SmcTuring.Appendix.Listing8ResetLayout

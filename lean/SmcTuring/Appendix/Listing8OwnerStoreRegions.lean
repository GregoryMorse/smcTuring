module
public import SmcTuring.Appendix.Listing8OwnerSequenceWrites
public import SmcTuring.Native.StringStoreTemplateRuns

public section
namespace SmcTuring.Appendix.Listing8OwnerStoreRegions
open Native Listing8Prototypes Listing8OwnerSequence

/-- Complete actual store fields, without a broad code interval. -/
@[expose] def Placement (mode : Mode) (owns : Nat → Nat → Prop) : Owner mode → Prop
  | .pointer source copied value => owns (Listing8CopiedPointer.selfField mode source copied) mode.wordBytes ∧ owns value.toNat mode.wordBytes
  | .scalar _ target _ => owns target 4

theorem pointer (mode : Mode) (owns : Nat → Nat → Prop) (source copied : Nat) (value : Word mode)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode copied)
    (sourceFits : source+pointerSpan mode<2^(8*mode.wordBytes)) (copiedFits : copied+pointerSpan mode<2^(8*mode.wordBytes))
    (selfOwned : owns (Listing8CopiedPointer.selfField mode source copied) mode.wordBytes)
    (targetOwned : owns value.toNat mode.wordBytes)
    (present : Current mode (.pointer source copied value) state.principal.memory) :
    StringStoreRegions.Run mode owns ((Listing8CopiedPointer.forms mode source copied value).map (StringWrites.liftString mode)) state := by
  have fieldFits : Listing8CopiedPointer.selfField mode source copied<2^(8*mode.wordBytes) := by
    cases mode <;> simp [Listing8CopiedPointer.selfField,pointerField,Listing8CopiedPointer.origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize]
      at sourceFits copiedFits ⊢ <;> omega
  have self : owns (Listing8CopiedPointer.label mode source copied).toNat mode.wordBytes := by
    change owns (Arithmetic.encodeNat mode (Listing8CopiedPointer.selfField mode source copied)).toNat mode.wordBytes
    rw [Arithmetic.encode_nat_toNat mode _ fieldFits];exact selfOwned
  have valueEq:=Listing8CopiedPointer.self_value mode source copied value state.principal.memory sourceFits copiedFits present.1 present.2
  have writes:=Reader.four_writes_owned mode state.principal (Listing8CopiedPointer.label mode source copied)
    (ReaderImage.firstDisp mode (Listing8CopiedPointer.origin mode source copied)) (ReaderImage.secondDisp mode)
    (Listing8CopiedPointer.first_hits mode source copied state.principal entry)
    (Listing8CopiedPointer.second_hits mode source copied state.principal entry)
    (fun address => owns address.toNat mode.wordBytes) self (by rw [valueEq];exact targetOwned)
  have actual : Writes.OwnedRun mode (fun address => owns address.toNat mode.wordBytes)
      [Listing8CopiedPointer.first mode source copied,Listing8CopiedPointer.second mode source copied,.exchangeIndirect,.moffs value] state.principal := by
    rw [←valueEq]
    simpa only [Writes.OwnedRun,and_true,Listing8CopiedPointer.first,Listing8CopiedPointer.second,Reader.swapped,Reader.restored,Reader.dereferenced] using writes
  have lifted:=StringStoreTemplateRuns.native mode owns _ state actual
  simpa only [Listing8CopiedPointer.forms,List.map_cons,List.map_nil,StringWrites.liftNative] using lifted

theorem advance (mode : Mode) (owns : Nat → Nat → Prop) (owner : Owner mode)
    (placed : Placement mode owns owner) (state : StringExecution.State mode) (valid : Valid mode owner)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner))
    (present : Current mode owner state.principal.memory) :
    StringStoreRegions.Run mode owns ((forms mode owner).map (StringStoreWrites.liftDword mode)) state := by
  cases owner with
  | pointer source copied value =>
    have mapping : ((Listing8CopiedPointer.forms mode source copied value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)=
        (Listing8CopiedPointer.forms mode source copied value).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
    change StringStoreRegions.Run mode owns
      (((Listing8CopiedPointer.forms mode source copied value).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)) state
    rw [mapping]
    exact pointer mode owns source copied value state entry valid.1 valid.2.1 placed.1 placed.2 present
  | scalar pc target value =>
    have packet:=StringStoreWrites.located mode target (target+4) pc target value state entry valid.2.2
      (by have bound:=valid.2.1;omega) ⟨Nat.le_refl _,Nat.le_refl _⟩
    have size:=StringStoreWrites.length mode (Relocation.memoryDisp mode (pc+10) target) value state
    have address : (StringWrites.packet mode (StringStoreWrites.liftDword mode
        (StringDword.store mode (Relocation.memoryDisp mode (pc+10) target) value)) state).address=target := by
      change 0<_ ∧ target≤_ ∧ _≤target+4 at packet
      omega
    refine ⟨?_,trivial⟩
    rw [address,size];exact placed

theorem regions (mode : Mode) (owns : Nat → Nat → Prop) (owners : List (Owner mode)) (start : Nat)
    (chain : Contiguous mode start owners) (valid : ∀ owner∈owners,Valid mode owner)
    (outside : ∀ writer∈owners,∀ reader∈owners,Listing8OwnerSequence.Outside mode writer reader)
    (placed : ∀ owner∈owners,Placement mode owns owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (present : Intact mode owners state.principal.memory) :
    StringStoreRegions.Run mode owns ((program mode owners).map (StringStoreWrites.liftDword mode)) state := by
  induction owners generalizing start state with
  | nil => trivial
  | cons owner owners ih =>
    have v:=valid owner (List.Mem.head _)
    have c:=present owner (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode (pc mode owner) := by rw [chain.1];exact entry
    have first:=advance mode owns owner (placed owner (List.Mem.head _)) state v location c
    have next:=advance_pc mode owner state v location c
    have kept : Intact mode owners (Listing8OwnerSequence.advance mode owner state).principal.memory := by
      intro reader member
      exact retained mode owner reader state v location c (present reader (List.mem_cons_of_mem _ member))
        (outside owner (List.Mem.head _) reader (List.mem_cons_of_mem _ member))
    have later:=ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer member reader inside => outside writer (List.mem_cons_of_mem _ member) reader (List.mem_cons_of_mem _ inside))
      (fun reader member => placed reader (List.mem_cons_of_mem _ member)) _ next kept
    rw [program,List.flatMap_cons,List.map_append,StringStoreRegions.append,
      Listing8OwnerSequenceWrites.advance_run mode owner state v location c]
    exact ⟨first,later⟩

end SmcTuring.Appendix.Listing8OwnerStoreRegions

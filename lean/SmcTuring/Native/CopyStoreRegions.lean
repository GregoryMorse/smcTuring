module
public import SmcTuring.Native.StringSequenceWrites
public import SmcTuring.Native.BoundedStoreRegions

public section
namespace SmcTuring.Native.CopyStoreRegions

theorem native (mode : Mode) (allowed : Nat → Nat → Prop) (forms : List (Native.Form mode))
    (state : StringExecution.State mode)
    (owned : Writes.OwnedRun mode (fun word => allowed word.toNat mode.wordBytes) forms state.principal) :
    StringStoreRegions.Run mode allowed (forms.map (StringWrites.liftNative mode)) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    have size : (StringWrites.packet mode (StringWrites.liftNative mode form) state).bytes.length=mode.wordBytes :=
      LittleEndian.word_encode_length _ _
    have address : (StringWrites.packet mode (StringWrites.liftNative mode form) state).address=
        (Writes.address mode form state.principal).toNat := rfl
    exact ⟨by rw [address,size];exact owned.1,ih (StringStack.execute mode (StringWrites.liftNative mode form) state) owned.2⟩

theorem copy (mode : Mode) (allowed : Nat → Nat → Prop) (forms : List (DwordCode.Form mode))
    (state : StringExecution.State mode)
    (owned : DwordCode.OwnedRun mode (fun address => allowed address 4) forms state.principal) :
    StringStoreRegions.Run mode allowed ((forms.map (StringDwordCopy.copy mode)).map (StringStoreWrites.liftDword mode)) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    constructor
    · simpa only [StringCopyWrites.copy_address,StringCopyWrites.copy_length] using owned.1
    · change StringStoreRegions.Run mode allowed _ (StringDword.execute mode (StringDwordCopy.copy mode form) state)
      rw [StringDwordCopy.copy_execute]
      exact ih _ owned.2

theorem word (mode : Mode) (allowed : Nat → Nat → Prop) (layout : ConversionLayout.Layout)
    (valid : ConversionLayout.Admissible mode layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (source : allowed layout.source mode.wordBytes) (destination : allowed layout.destination mode.wordBytes) :
    StringStoreRegions.Run mode allowed ((StringDwordCopy.wordProgram mode layout).map (StringStoreWrites.liftDword mode)) state := by
  have positive : 0<mode.wordBytes := by cases mode <;> decide
  have sourceFits : layout.source<2^(8*mode.wordBytes) := by have fits:=valid.sourceFits;omega
  have destinationFits : layout.destination<2^(8*mode.wordBytes) := by have fits:=valid.destinationFits;omega
  have actual:=ConversionOwnership.supported_run mode layout valid state.principal entry
    (fun value => allowed value.toNat mode.wordBytes)
    (by rw [Arithmetic.encode_nat_toNat mode layout.source sourceFits];exact source)
    (by rw [Arithmetic.encode_nat_toNat mode layout.destination destinationFits];exact destination)
  have mapped : ((StringDwordCopy.wordProgram mode layout).map (StringStoreWrites.liftDword mode))=
      (ConversionLayout.program mode layout).map (StringWrites.liftNative mode) := by
    rw [StringDwordCopy.wordProgram,List.map_map];rfl
  rw [mapped]
  exact native mode allowed _ state actual

theorem dword (mode : Mode) (allowed : Nat → Nat → Prop) (layout : DwordLayout.Layout)
    (valid : DwordLayout.Admissible mode layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (source : allowed layout.source 4) (destination : allowed layout.destination 4) :
    StringStoreRegions.Run mode allowed ((StringDwordCopy.dwordProgram mode layout).map (StringStoreWrites.liftDword mode)) state :=
  copy mode allowed _ state (DwordImage.supported_run mode layout valid state.principal entry _ source destination)

theorem sequence (mode : Mode) (allowed : Nat → Nat → Prop) (layouts : List DwordLayout.Layout) (start : Nat)
    (chain : StringDwordSequence.Contiguous mode start layouts)
    (valid : ∀ layout∈layouts,DwordLayout.Admissible mode layout)
    (fields : ∀ layout∈layouts,allowed layout.source 4 ∧ allowed layout.destination 4)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringStoreRegions.Run mode allowed ((StringDwordSequence.program mode layouts).map (StringStoreWrites.liftDword mode)) state := by
  induction layouts generalizing start state with
  | nil => trivial
  | cons layout layouts ih =>
    have v:=valid layout (List.Mem.head _)
    have f:=fields layout (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode layout.start := by rw [chain.1];exact entry
    have first:=dword mode allowed layout v state location f.1 f.2
    have next : (StringDwordCopy.dwordFinish mode layout state).principal.pc=Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      change (DwordEffects.finish mode layout state.principal).pc=_
      rw [DwordEffects.effect mode layout v state.principal location]
    have rest:=ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
      (fun later member => fields later (List.Mem.tail _ member)) _ next
    rw [StringDwordSequence.program,List.flatMap_cons,List.map_append,StringStoreRegions.append,StringSequenceWrites.dword_run]
    exact ⟨first,rest⟩

end SmcTuring.Native.CopyStoreRegions

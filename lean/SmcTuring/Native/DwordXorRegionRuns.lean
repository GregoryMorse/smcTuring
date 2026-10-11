module
public import SmcTuring.Native.StringStoreRegions
public import SmcTuring.Native.DwordXorWrites

public section
namespace SmcTuring.Native.DwordXorRegionRuns

theorem helper (mode : Mode) (allowed : Nat → Nat → Prop) (layout : DwordXorHelper.Layout)
    (valid : DwordXorHelper.Admissible mode layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (source : allowed layout.source 4) (destination : allowed layout.destination 4) :
    StringStoreRegions.Run mode allowed
      ((DwordXorHelper.program mode layout).map (StringStoreWrites.liftDword mode)) state := by
  have sourceFits : layout.source<2^(8*mode.wordBytes) := by have bound := valid.sourceFits;omega
  have targetFits : layout.destination<2^(8*mode.wordBytes) := by have bound := valid.destinationFits;omega
  have first := StringStoreRegions.bounded_packet mode allowed layout.source _ state
    (DwordXorWrites.exchange_write mode layout.source (layout.source+4) layout.start layout.source state entry
      valid.firstRange sourceFits ⟨Nat.le_refl _,Nat.le_refl _⟩)
    (by simpa only [StringMixed.canonical,MixedDword.width] using
      StringMixedWrites.length mode (.copy (.exchange (Relocation.memoryDisp mode (layout.start+6) layout.source))) state) source
  let swapped : StringExecution.State mode := {state with principal:=DwordXorHelper.swapped mode layout state.principal}
  let xored : StringExecution.State mode := {state with principal:=DwordXorHelper.xored mode layout state.principal}
  have secondPC : swapped.principal.pc=Arithmetic.encodeNat mode (layout.start+6) := by
    dsimp only [swapped]
    rw [DwordXorHelper.first_effect mode layout valid state.principal entry]
  have second := StringStoreRegions.bounded_packet mode allowed layout.destination _ swapped
    (DwordXorWrites.xor_write mode layout.destination (layout.destination+4) (layout.start+6) layout.destination swapped secondPC
      (by simpa only [Nat.add_assoc] using valid.middleRange) targetFits ⟨Nat.le_refl _,Nat.le_refl _⟩)
    (DwordXorWrites.length mode _ swapped) destination
  have thirdPC : xored.principal.pc=Arithmetic.encodeNat mode (layout.start+12) := by
    dsimp only [xored]
    rw [DwordXorHelper.middle_effect mode layout valid state.principal entry]
  have third := StringStoreRegions.bounded_packet mode allowed layout.source _ xored
    (DwordXorWrites.exchange_write mode layout.source (layout.source+4) (layout.start+12) layout.source xored thirdPC
      (by simpa only [DwordXorHelper.endPC,Nat.add_assoc] using valid.thirdRange) sourceFits ⟨Nat.le_refl _,Nat.le_refl _⟩)
    (by simpa only [StringMixed.canonical,MixedDword.width] using
      StringMixedWrites.length mode (.copy (.exchange (Relocation.memoryDisp mode (layout.start+12+6) layout.source))) xored) source
  constructor
  · exact first
  · change StringStoreRegions.Run mode allowed _
      (StringDword.execute mode (StringDwordCopy.copy mode (DwordXorHelper.first mode layout)) state)
    rw [StringDwordCopy.copy_execute]
    constructor
    · simpa only [swapped,DwordXorHelper.swapped,DwordXorHelper.middle,Nat.add_assoc,Nat.reduceAdd] using second
    · change StringStoreRegions.Run mode allowed _
        (StringDword.execute mode (StringDwordXor.canonical mode (DwordXorHelper.middle mode layout)) swapped)
      rw [StringDwordXor.execute]
      exact ⟨by simpa only [xored,swapped,DwordXorHelper.xored,DwordXorHelper.swapped,DwordXorHelper.third,
        DwordXorHelper.endPC,Nat.add_assoc,Nat.reduceAdd] using third,trivial⟩

theorem sequence (mode : Mode) (allowed : Nat → Nat → Prop) (layouts : List DwordXorHelper.Layout) (start : Nat)
    (chain : DwordXorSequence.Contiguous start layouts)
    (valid : ∀ layout∈layouts,DwordXorHelper.Admissible mode layout)
    (fields : ∀ layout∈layouts,allowed layout.source 4 ∧ allowed layout.destination 4)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringStoreRegions.Run mode allowed ((DwordXorSequence.program mode layouts).map (StringStoreWrites.liftDword mode)) state := by
  induction layouts generalizing start state with
  | nil => trivial
  | cons layout rest ih =>
    have v := valid layout (List.Mem.head _)
    have here : state.principal.pc=Arithmetic.encodeNat mode layout.start := by rw [chain.1];exact entry
    have first := helper mode allowed layout v state here (fields layout (List.Mem.head _)).1 (fields layout (List.Mem.head _)).2
    have next : (DwordXorHelper.stringFinish mode layout state).principal.pc=Arithmetic.encodeNat mode (DwordXorHelper.endPC layout) := by
      change (DwordXorHelper.finish mode layout state.principal).pc=_
      rw [DwordXorHelper.effect mode layout v state.principal here]
    rw [DwordXorSequence.program,List.flatMap_cons,List.map_append,StringStoreRegions.append,DwordXorWrites.helper_run]
    exact ⟨first,ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
      (fun later member => fields later (List.Mem.tail _ member)) _ next⟩

theorem packets (mode : Mode) (allowed : Nat → Nat → Prop) (sites : List DwordPackets.Site) (start : Nat)
    (chain : DwordPackets.Contiguous start sites) (valid : ∀ site∈sites,DwordPackets.Valid mode site)
    (fields : ∀ site∈sites,allowed site.target 4) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringStoreRegions.Run mode allowed ((DwordPackets.program mode sites state.principal).map (StringStoreWrites.liftDword mode)) state := by
  induction sites generalizing start state with
  | nil => trivial
  | cons site rest ih =>
    have v := valid site (List.Mem.head _)
    have here : state.principal.pc=Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    have first := DwordPacketTemplateRuns.located mode site v state.principal here allowed (fields site (List.Mem.head _))
    have next : (DwordPackets.execute mode site state.principal).pc=Arithmetic.encodeNat mode (site.pc+DwordPackets.size site) := by
      rw [DwordPackets.effect mode site v state.principal here]
    constructor
    · change allowed (StringWrites.packet mode (StringStoreWrites.liftDword mode
        (StringMixed.canonical mode (.arithmetic (DwordPackets.live mode site state.principal.memory)))) state).address
        (StringWrites.packet mode (StringStoreWrites.liftDword mode
          (StringMixed.canonical mode (.arithmetic (DwordPackets.live mode site state.principal.memory)))) state).bytes.length
      simpa only [StringMixedWrites.address,StringMixedWrites.length] using first
    · change StringStoreRegions.Run mode allowed _
        (StringDword.execute mode (StringDwordArithmetic.canonical mode (DwordPackets.live mode site state.principal.memory)) state)
      rw [StringDwordArithmetic.execute]
      exact ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
        (fun later member => fields later (List.Mem.tail _ member))
        {state with principal:=DwordPackets.execute mode site state.principal} next

end SmcTuring.Native.DwordXorRegionRuns

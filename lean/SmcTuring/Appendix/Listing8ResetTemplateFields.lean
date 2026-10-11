module
public import SmcTuring.Appendix.Listing8ResetStoreRegions
public import SmcTuring.Native.WordCopyTemplates
public import SmcTuring.Native.RelativeCallTemplate
public import SmcTuring.Native.DwordTemplateCollection

public section
namespace SmcTuring.Appendix.Listing8ResetTemplateFields
open Native Listing8ResetLayout

@[expose] def fixed (mode : Mode) (l : Layout) :=
  WordCopyTemplates.entries mode (inputCopy mode l)++WordCopyTemplates.entries mode (transitionCopy mode l)
@[expose] def arithmetic (mode : Mode) (l : Layout) : List DwordTemplateCollection.Template :=
  [.binary .store l.start,.binary .store (markerPC mode l)]

/-- Additional static separation, proved from the actual packed graph in the
bindings. It concerns original addresses only, never future execution. -/
structure Separation (mode : Mode) (l : Layout) : Prop where
  tableOutside : l.ttape+mode.wordBytes≤l.start ∨ endPC mode l≤l.ttape
  sourceCall : l.inputSource+mode.wordBytes≤l.callPC
  inputCall : l.inputCursor+mode.wordBytes≤l.callPC
  transitionCall : l.transitionCursor+mode.wordBytes≤l.callPC
  tableCall : l.ttape+mode.wordBytes≤l.callPC ∨ l.callPC+1≤l.ttape

theorem fixed_count (mode : Mode) (l : Layout) : (fixed mode l).length=6 := by
  rw [fixed,List.length_append,WordCopyTemplates.count,WordCopyTemplates.count]

theorem fixed_legal (mode : Mode) (l : Layout) :
    ∀ entry∈fixed mode l,FixedStackTemplates.Legal mode entry.instruction := by
  intro entry member
  rcases List.mem_append.mp member with a | b
  · exact WordCopyTemplates.legal mode _ entry a
  · exact WordCopyTemplates.legal mode _ entry b

theorem fixed_initial (mode : Mode) (l : Layout) (memory : ByteMemory.Memory)
    (initial : Listing8ResetPackets.Initial mode l memory) : FixedStackTemplates.All mode (fixed mode l) memory := by
  intro entry member
  rcases List.mem_append.mp member with a | b
  · exact WordCopyTemplates.initial mode _ memory (Listing8ResetPackets.input_current mode l memory initial) entry a
  · exact WordCopyTemplates.initial mode _ memory (Listing8ResetPackets.transition_current mode l memory initial) entry b

theorem fixed_frames (mode : Mode) (l : Layout) (bounds : Bounds mode l) (separation : Separation mode l)
    (address count : Nat) (allowed : Listing8ResetStoreRegions.Allowed mode l address count) :
    FixedStackTemplates.OutsideAll mode (fixed mode l) address count := by
  have external1:=bounds.callBefore
  have external2:=bounds.inputSourceBeforeCall
  have external3:=bounds.inputCursorBefore
  have external4:=bounds.transitionCursorBefore
  have tableOutside:=separation.tableOutside
  have coords:=positions mode l
  intro entry member
  rcases List.mem_append.mp member with a | b
  · have window:=WordCopyTemplates.bounds mode (inputCopy mode l) entry a
    change l.start+10≤entry.pc ∧ entry.pc+(FixedStackTemplates.encode mode entry.instruction).length≤ownerPC mode l at window
    simp only [Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
    rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals cases mode
    all_goals simp only [reduceCtorEq,ite_true,ite_false,Mode.wordBytes,StringInit.field,StringCodec.fieldOffset,Listing8ResetLayout.endPC] at *
    all_goals omega
  · have window:=WordCopyTemplates.bounds mode (transitionCopy mode l) entry b
    change ownerPC mode l+StringCodec.initialSize mode≤entry.pc ∧ entry.pc+(FixedStackTemplates.encode mode entry.instruction).length≤markerPC mode l at window
    simp only [Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
    rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals cases mode
    all_goals simp only [reduceCtorEq,ite_true,ite_false,Mode.wordBytes,StringInit.field,StringCodec.fieldOffset,StringCodec.initialSize,Listing8ResetLayout.endPC] at *
    all_goals omega

theorem arithmetic_compatible (mode : Mode) (l : Layout) (bounds : Bounds mode l) (separation : Separation mode l)
    (address count : Nat) (allowed : Listing8ResetStoreRegions.Allowed mode l address count) :
    DwordTemplateCollection.CompatibleAll (arithmetic mode l) address count := by
  have external1:=bounds.callBefore
  have external2:=bounds.inputSourceBeforeCall
  have external3:=bounds.inputCursorBefore
  have external4:=bounds.transitionCursorBefore
  have tableOutside:=separation.tableOutside
  have coords:=positions mode l
  intro descriptor member
  simp only [arithmetic,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals simp only [Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
  all_goals rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals cases mode
  all_goals simp only [DwordTemplateCollection.Compatible,DwordTemplateCollection.field,DwordTemplateCollection.width,DwordTemplateCollection.start,DwordTemplateCollection.span,reduceCtorEq,ite_true,ite_false,Mode.wordBytes,StringInit.field,StringCodec.fieldOffset,Listing8ResetLayout.endPC] at *
  all_goals omega

theorem owner_frames (mode : Mode) (l : Layout) (bounds : Bounds mode l) (separation : Separation mode l)
    (address count : Nat) (allowed : Listing8ResetStoreRegions.Allowed mode l address count) :
    address+count≤ownerPC mode l ∨ StringInit.field mode (ownerPC mode l)≤address := by
  have external1:=bounds.callBefore
  have external2:=bounds.inputSourceBeforeCall
  have external3:=bounds.inputCursorBefore
  have external4:=bounds.transitionCursorBefore
  have tableOutside:=separation.tableOutside
  have coords:=positions mode l
  simp only [Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
  rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals cases mode
  all_goals simp only [reduceCtorEq,ite_true,ite_false,Mode.wordBytes,StringInit.field,StringCodec.fieldOffset,Listing8ResetLayout.endPC] at *
  all_goals omega

theorem call_frames (mode : Mode) (l : Layout) (bounds : Bounds mode l) (separation : Separation mode l)
    (address count : Nat) (allowed : Listing8ResetStoreRegions.Allowed mode l address count) :
    address+count≤l.callPC ∨ l.callPC+1≤address := by
  have external:=bounds.callBefore
  have source:=separation.sourceCall
  have input:=separation.inputCall
  have transition:=separation.transitionCall
  have tableOutside:=separation.tableCall
  have coords:=positions mode l
  simp only [Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
  rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals cases mode
  all_goals simp only [reduceCtorEq,ite_true,ite_false,Mode.wordBytes,StringInit.field,StringCodec.fieldOffset,Listing8ResetLayout.endPC] at *
  all_goals omega

end SmcTuring.Appendix.Listing8ResetTemplateFields

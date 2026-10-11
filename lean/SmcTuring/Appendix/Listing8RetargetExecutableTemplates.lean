module
public import SmcTuring.Native.DwordTemplateCollection
public import SmcTuring.Native.MixedFieldOwnership
public import SmcTuring.Appendix.Listing8ModeOffsets

public section
namespace SmcTuring.Appendix.Listing8RetargetExecutableTemplates
open Native Listing8ModeOffsets DwordTemplateCollection

@[expose] def templates (mode : Mode) (layout : Layout) : List Template :=
  (sites mode layout).map (fun site => .binary .store site.pc) ++
    (sites mode layout).map (fun site => .binary .store site.owner)

theorem bounds (mode : Mode) (layout : Layout) (template : Template) (member : template∈templates mode layout) :
    layout.start≤start template ∧ start template+span template≤endPC mode layout := by
  simp only [templates,List.mem_append] at member
  rcases member with patch | owner
  · rcases List.mem_map.mp patch with ⟨site,inside,rfl⟩
    have geometry := owners_after_patches mode layout site inside
    have order : layout.start≤site.pc := by
      simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl <;> simp
    exact ⟨order,by change site.pc+10≤endPC mode layout;omega⟩
  · rcases List.mem_map.mp owner with ⟨site,inside,rfl⟩
    have geometry := owners_after_patches mode layout site inside
    exact ⟨by change layout.start≤site.owner;omega,geometry.2.1⟩

theorem patch_compatible (mode : Mode) (layout : Layout) (writer : Site) (written : writer∈sites mode layout) :
    CompatibleAll (templates mode layout) (writer.owner+2) 4 := by
  intro template member
  simp only [templates,List.mem_append] at member
  rcases member with patch | owner
  · rcases List.mem_map.mp patch with ⟨reader,inside,rfl⟩
    have w := owners_after_patches mode layout writer written
    have r := owners_after_patches mode layout reader inside
    right;right
    change reader.pc+10≤writer.owner+2
    omega
  · rcases List.mem_map.mp owner with ⟨reader,inside,rfl⟩
    by_cases same : writer=reader
    · subst reader
      left
      change writer.owner+2≤writer.owner+2 ∧ writer.owner+2+4≤writer.owner+2+8
      exact ⟨Nat.le_refl _,by omega⟩
    · exact Or.inr (owners_separate mode layout writer reader written inside same)

theorem owned (mode : Mode) (allSites : List Site) (startPC : Nat)
    (chain : DwordRetargetSequence.Contiguous startPC allSites)
    (valid : ∀ site∈allSites,DwordRetargetSequence.Valid mode site)
    (owns : Nat → Nat → Prop) (fields : ∀ site∈allSites,owns (site.owner+2) 4)
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode startPC) :
    MixedDword.OwnedRun mode owns (DwordRetargetSequence.program mode allSites) state := by
  induction allSites generalizing startPC state with
  | nil => trivial
  | cons site rest ih =>
    have v := valid site (List.Mem.head _)
    have location : state.pc=Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    have first := MixedFieldOwnership.located mode site.pc (site.owner+2)
      (.store 0 (DwordRetarget.printed mode site.pc site.owner site.destination)) state rfl location v.2.2
      (by have fits := v.2.1;omega) owns (fields site (List.Mem.head _))
    have next : (DwordRetarget.patched mode site.pc site.owner site.destination state).pc=Arithmetic.encodeNat mode (site.pc+10) := by
      rw [DwordRetarget.patch_effect mode site.pc site.owner site.destination state location v.2.2 (by have fits := v.2.1;omega)]
    exact ⟨first,ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
      (fun later member => fields later (List.Mem.tail _ member)) _ next⟩

theorem initial (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next transitionState : Word mode)
    (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState).length=
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState) :
    All (templates mode layout) memory := by
  have patches := initial_patches mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState memory current
  have owners := source_owners mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState memory current
  intro template member
  simp only [templates,List.mem_append] at member
  rcases member with patch | owner
  · rcases List.mem_map.mp patch with ⟨site,inside,rfl⟩
    exact DwordOperandTemplates.initial .store site.pc _ (DwordRetarget.printed mode site.pc site.owner site.destination) memory (patches site inside)
  · rcases List.mem_map.mp owner with ⟨site,inside,rfl⟩
    simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl
    · exact DwordOperandTemplates.initial .store _ _ tape memory owners.1
    · exact DwordOperandTemplates.initial .store _ _ rule memory owners.2.1
    · exact DwordOperandTemplates.initial .store _ _ fresh memory owners.2.2.1
    · exact DwordOperandTemplates.initial .store _ _ direction memory owners.2.2.2

/-- Every actual one of the four printed retarget stores preserves the
original opcodes of all patch instructions and all four copied scalar owners. -/
theorem all_states (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next transitionState : Word mode)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : ByteMemory.bytesAt state.principal.memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState).length=
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState) :
    StringTemplateStates.Run mode (fun reached => All (templates mode layout) reached.principal.memory)
      (((DwordRetargetSequence.program mode (sites mode layout)).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  DwordTemplateCollection.all_states mode _ _ state
    (initial mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState _ current)
    (owned mode _ layout.start (chain mode layout) (valid mode layout capacity (patch_ranges mode layout))
      _ (patch_compatible mode layout) state.principal entry)

theorem all_decodes (mode : Mode) (layout : Layout) (sourceNode sourceTransition : Nat)
    (tape rule fresh direction : Dword) (back forward next transitionState : Word mode)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : ByteMemory.bytesAt state.principal.memory layout.start
      (bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState).length=
      bytes mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState) :
    StringTemplateStates.Run mode (fun reached => ∀ template∈templates mode layout,Decodes mode template reached.principal.memory)
      (((DwordRetargetSequence.program mode (sites mode layout)).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun reached all template member => decodes mode template reached.principal.memory (all template member))
    (all_states mode layout sourceNode sourceTransition tape rule fresh direction back forward next transitionState capacity state entry current)

end SmcTuring.Appendix.Listing8RetargetExecutableTemplates

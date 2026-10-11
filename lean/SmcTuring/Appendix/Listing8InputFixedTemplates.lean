module
public import SmcTuring.Native.MixedFixedTemplates
public import SmcTuring.Appendix.Listing8InputExecutableTemplates

public section
namespace SmcTuring.Appendix.Listing8InputFixedTemplates
open Native Listing8LiteralInput MixedFixedTemplates

@[expose] def cursorEntries (mode : Mode) (layout : Layout) : List (Entry mode) :=
  [⟨(InputUpdate.body (updateLayout mode layout)).start,CursorLayout.first mode (InputUpdate.body (updateLayout mode layout))⟩,
   ⟨CursorLayout.lastPC mode (InputUpdate.body (updateLayout mode layout)),CursorLayout.last mode (InputUpdate.body (updateLayout mode layout))⟩]
@[expose] def entries (mode : Mode) (layout : Layout) : List (Entry mode) :=
  copyEntries mode (copyLayout mode layout) ++
    (distributionLayouts mode layout).flatMap (copyEntries mode) ++ cursorEntries mode layout

theorem first_copy_bounds (mode : Mode) (layout : Layout) (entry : Entry mode)
    (member : entry∈copyEntries mode (copyLayout mode layout)) :
    layout.start≤entry.pc ∧ entry.pc+span mode entry≤ownerPC mode layout := by
  have range := copy_bounds mode (copyLayout mode layout) entry member
  simp only [copyLayout,DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,
    ownerPC,copyStart,DwordLayout.span] at range ⊢
  omega

theorem distribution_bounds (mode : Mode) (layout : Layout) (entry : Entry mode)
    (member : entry∈(distributionLayouts mode layout).flatMap (copyEntries mode)) :
    distributionStart mode layout≤entry.pc ∧ entry.pc+span mode entry≤updateStart mode layout := by
  rcases List.mem_flatMap.mp member with ⟨helper,inside,packet⟩
  have a := copy_bounds mode helper entry packet
  have b := Listing8LiteralMaskTrace.helper_bounds mode layout helper inside
  omega

theorem bounds (mode : Mode) (layout : Layout) (entry : Entry mode) (member : entry∈entries mode layout) :
    layout.start≤entry.pc ∧ entry.pc+span mode entry≤endPC mode layout := by
  simp only [entries,List.mem_append] at member
  rcases member with (first | distribution) | cursor
  · have range := first_copy_bounds mode layout entry first
    simp only [endPC,updateStart,distributionStart] at *
    omega
  · have range := distribution_bounds mode layout entry distribution
    simp only [endPC,distributionStart,ownerPC,copyStart] at *
    omega
  · simp only [cursorEntries,List.mem_cons,List.not_mem_nil,or_false] at cursor
    rcases cursor with rfl | rfl <;> cases mode <;>
      simp [span,MixedDword.encode_length,MixedDword.length,MixedDword.exchange,DwordCode.length,
        CursorLayout.first,CursorLayout.last,CursorLayout.lastPC,CursorLayout.middlePC,CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,
        updateLayout,InputUpdate.body,endPC,InputUpdate.span,CursorImage.span,updateStart,distributionStart,
        ownerPC,copyStart,gap,DwordLayout.span,DwordLayout.storeSize] <;> omega

theorem internal_fields (mode : Mode) (layout : Layout) (address : Nat)
    (chosen : address=scalarField mode layout ∨ address=sourceField mode layout ∨
      address=maskField mode layout ∨ address=pendingField mode layout) :
    OutsideAll mode (entries mode layout) address 4 := by
  intro entry member
  simp only [entries,List.mem_append] at member
  rcases member with (first | distribution) | cursor
  · have range := first_copy_bounds mode layout entry first
    right
    rcases chosen with rfl | rfl | rfl | rfl <;>
      cases mode <;> simp [scalarField,sourceField,maskField,pendingField,updateLayout,InputUpdate.field,
        InputUpdate.body,CursorPatch.field,CursorLayout.middlePC,CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,updateStart,
        distributionStart,gap] at * <;> omega
  · have range := distribution_bounds mode layout entry distribution
    rcases chosen with rfl | rfl | rfl | rfl <;>
      cases mode <;> simp [Outside,scalarField,sourceField,maskField,pendingField,updateLayout,InputUpdate.field,
        InputUpdate.body,CursorPatch.field,CursorLayout.middlePC,CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,updateStart,
        distributionStart,gap] at * <;> omega
  · simp only [cursorEntries,List.mem_cons,List.not_mem_nil,or_false] at cursor
    rcases cursor with rfl | rfl <;> rcases chosen with rfl | rfl | rfl | rfl <;>
      cases mode <;> simp [Outside,span,MixedDword.encode_length,MixedDword.length,MixedDword.exchange,DwordCode.length,
        CursorLayout.first,CursorLayout.last,CursorLayout.lastPC,CursorLayout.middlePC,CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,
        scalarField,sourceField,maskField,pendingField,updateLayout,InputUpdate.field,InputUpdate.body,CursorPatch.field,
        updateStart,distributionStart,gap]

theorem exterior (mode : Mode) (layout : Layout) (address count : Nat)
    (outside : address+count≤layout.start ∨ endPC mode layout≤address) :
    OutsideAll mode (entries mode layout) address count := by
  intro entry member
  have range := bounds mode layout entry member
  rcases outside with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem owned_fields (mode : Mode) (layout : Layout) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (outside : Listing8LiteralComposition.DataOutside mode layout) :
    Listing8InputTemplateRegions.Fields mode layout (OutsideAll mode (entries mode layout)) := by
  refine ⟨internal_fields mode layout _ (Or.inl rfl),
    internal_fields mode layout _ (Or.inr (Or.inl rfl)),
    internal_fields mode layout _ (Or.inr (Or.inr (Or.inl rfl))),
    internal_fields mode layout _ (Or.inr (Or.inr (Or.inr rfl))),
    exterior mode layout _ _ outside.cursor,exterior mode layout _ _ (by simpa only [Nat.add_assoc] using outside.tape),?_⟩
  intro helper member
  exact exterior mode layout _ _ (masks.outsideInput helper member)

theorem initial (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) (intact : Listing8LiteralInput.Intact mode layout candidate ruleOld targetOld fresh memory) :
    All mode (entries mode layout) memory := by
  have first := copy_initial mode (copyLayout mode layout) memory (copy_current mode layout candidate ruleOld targetOld fresh memory intact)
  have distribution := Listing8LiteralMaskTrace.initial_helpers mode layout memory
    (distribution_current mode layout candidate ruleOld targetOld fresh memory intact)
  have cursor := InputUpdate.body_current mode (updateLayout mode layout) targetOld fresh false memory
    (update_current mode layout candidate ruleOld targetOld fresh memory intact)
  intro entry member
  simp only [entries,List.mem_append] at member
  rcases member with (a | b) | c
  · exact first entry a
  · rcases List.mem_flatMap.mp b with ⟨helper,inside,packet⟩
    exact copy_initial mode helper memory (distribution helper inside) entry packet
  · simp only [cursorEntries,List.mem_cons,List.not_mem_nil,or_false] at c
    rcases c with rfl | rfl
    · exact CursorImage.first_current mode _ targetOld memory cursor
    · exact CursorImage.last_current mode _ targetOld memory cursor

theorem mask_initial (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (memory : ByteMemory.Memory) (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask memory) :
    All mode (entries mode layout) memory := by
  have normalized := initial mode layout rule tape pending fresh _
    (Listing8InputMask.zero_intact mode layout rule tape pending fresh oldMask memory current)
  have back := store_all mode (entries mode layout) (DwordCode.put memory (maskField mode layout) 0)
    (maskField mode layout) (LittleEndian.wordEncode 4 oldMask) normalized
    (by rw [LittleEndian.word_encode_length];exact internal_fields mode layout _ (Or.inr (Or.inr (Or.inl rfl))))
  change All mode (entries mode layout) (DwordCode.put (DwordCode.put memory (maskField mode layout) 0) (maskField mode layout) oldMask) at back
  rw [DwordCode.put_overwrite,←Listing8InputExecutableTemplates.mask_operand mode layout rule tape pending fresh oldMask memory current,
    DwordCode.put_get_back] at back
  exact back

theorem all_states (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    StringTemplateStates.Run mode (fun reached => All mode (entries mode layout) reached.principal.memory)
      (((Listing8LiteralComposition.program mode layout rule tape fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  MixedFixedTemplates.all_states mode _ _ state (mask_initial mode layout rule tape pending fresh oldMask _ current)
    (Listing8InputTemplateRegions.mask_complete mode layout rule tape pending fresh oldMask capacity masks update outside
      state.principal entry current cursor _ (owned_fields mode layout masks outside))

theorem all_decodes (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    StringTemplateStates.Run mode (fun reached => ∀ packet∈entries mode layout,Decodes mode packet reached.principal.memory)
      (((Listing8LiteralComposition.program mode layout rule tape fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun reached all packet member => decodes mode packet reached.principal.memory (all packet member))
    (all_states mode layout rule tape pending fresh oldMask capacity masks update outside state entry current cursor)

end SmcTuring.Appendix.Listing8InputFixedTemplates

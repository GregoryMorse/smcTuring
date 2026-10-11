module
public import SmcTuring.Appendix.Listing8InputTemplateRegions

public section
namespace SmcTuring.Appendix.Listing8InputExecutableTemplates
open Native Listing8LiteralInput DwordTemplateCollection

@[expose] def templates (mode : Mode) (layout : Layout) : List Template :=
  [.binary .store layout.start,
   .binary .store (ownerPC mode layout),
   .binary .subtract (ownerPC mode layout+10),
   .unary .negate (ownerPC mode layout+20),
   .unary .sbbZero (ownerPC mode layout+26),
   .unary .complement (ownerPC mode layout+33),
   .binary .bitXor (updateStart mode layout),
   .binary .bitAnd (updateStart mode layout+10),
   .unary .xorAtAccumulator (CursorLayout.middlePC mode (InputUpdate.body (updateLayout mode layout)))]

theorem bounds (mode : Mode) (layout : Layout) (template : Template) (member : template∈templates mode layout) :
    layout.start≤start template ∧ start template+span template≤endPC mode layout := by
  simp only [templates,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases mode <;> simp [start,span,DwordUnaryTemplates.span,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,
      ownerPC,copyStart,updateStart,distributionStart,gap,endPC,DwordLayout.span,DwordLayout.storeSize,
      updateLayout,InputUpdate.body,InputUpdate.span,CursorImage.span,CursorLayout.middlePC,CursorLayout.exchangeSize] <;> omega

theorem internal_fields (mode : Mode) (layout : Layout) (address : Nat)
    (chosen : address=scalarField mode layout ∨ address=sourceField mode layout ∨
      address=maskField mode layout ∨ address=pendingField mode layout) :
    CompatibleAll (templates mode layout) address 4 := by
  intro template member
  simp only [templates,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases chosen with rfl | rfl | rfl | rfl <;>
    cases mode <;> simp [Compatible,start,span,field,width,DwordUnaryTemplates.span,DwordUnaryTemplates.field,
      DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,scalarField,sourceField,maskField,pendingField,
      ownerPC,copyStart,updateStart,distributionStart,gap,DwordLayout.span,DwordLayout.storeSize,
      updateLayout,InputUpdate.body,InputUpdate.field,CursorPatch.field,CursorLayout.middlePC,CursorLayout.exchangeSize] <;> omega

theorem exterior (mode : Mode) (layout : Layout) (address count : Nat)
    (outside : address+count≤layout.start ∨ endPC mode layout≤address) :
    CompatibleAll (templates mode layout) address count := by
  intro template member
  have range := bounds mode layout template member
  right
  rcases outside with before | after
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem owned_fields (mode : Mode) (layout : Layout) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (outside : Listing8LiteralComposition.DataOutside mode layout) :
    Listing8InputTemplateRegions.Fields mode layout (CompatibleAll (templates mode layout)) := by
  refine ⟨internal_fields mode layout _ (Or.inl rfl),
    internal_fields mode layout _ (Or.inr (Or.inl rfl)),
    internal_fields mode layout _ (Or.inr (Or.inr (Or.inl rfl))),
    internal_fields mode layout _ (Or.inr (Or.inr (Or.inr rfl))),
    exterior mode layout _ _ outside.cursor,exterior mode layout _ _ (by simpa only [Nat.add_assoc] using outside.tape),?_⟩
  intro helper member
  exact exterior mode layout _ _ (masks.outsideInput helper member)

theorem initial (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) (intact : Listing8LiteralInput.Intact mode layout candidate ruleOld targetOld fresh memory) :
    All (templates mode layout) memory := by
  have tail := tail_current mode layout candidate ruleOld targetOld fresh memory intact
  have update := update_current mode layout candidate ruleOld targetOld fresh memory intact
  intro template member
  simp only [templates,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact DwordOperandTemplates.initial .store layout.start _ 0 memory
      (reset_current mode layout candidate ruleOld targetOld fresh memory intact)
  · exact DwordOperandTemplates.initial .store (ownerPC mode layout) _ candidate memory
      (owner_current mode layout candidate ruleOld targetOld fresh memory intact)
  · have packet := DwordComparisonTail.current_packet mode (tailLayout mode layout) ruleOld memory tail 0
    apply DwordOperandTemplates.initial .subtract (ownerPC mode layout+10) _ ruleOld memory
    simpa [tailLayout,DwordComparisonTail.offset,DwordComparisonTail.form,DwordComparisonTail.raw,
      DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.encode_length,DwordArithmetic.length,DwordOperandTemplates.form] using packet
  · have packet := DwordComparisonTail.current_packet mode (tailLayout mode layout) ruleOld memory tail 1
    apply DwordUnaryTemplates.initial .negate (ownerPC mode layout+20) _ memory
    simpa [tailLayout,DwordComparisonTail.offset,DwordComparisonTail.form,DwordComparisonTail.raw,
      DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.encode_length,DwordArithmetic.length,
      DwordUnaryTemplates.form,DwordUnaryTemplates.span,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,List.length_cons,List.length_nil] using packet
  · have packet := DwordComparisonTail.current_packet mode (tailLayout mode layout) ruleOld memory tail 2
    apply DwordUnaryTemplates.initial .sbbZero (ownerPC mode layout+26) _ memory
    simpa [tailLayout,DwordComparisonTail.offset,DwordComparisonTail.form,DwordComparisonTail.raw,
      DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.encode_length,DwordArithmetic.length,
      DwordUnaryTemplates.form,DwordUnaryTemplates.span,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,List.length_cons,List.length_nil] using packet
  · have packet := DwordComparisonTail.current_packet mode (tailLayout mode layout) ruleOld memory tail 3
    apply DwordUnaryTemplates.initial .complement (ownerPC mode layout+33) _ memory
    simpa [tailLayout,DwordComparisonTail.offset,DwordComparisonTail.form,DwordComparisonTail.raw,
      DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.encode_length,DwordArithmetic.length,
      DwordUnaryTemplates.form,DwordUnaryTemplates.span,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,List.length_cons,List.length_nil] using packet
  · exact DwordOperandTemplates.initial .bitXor (updateStart mode layout) _ fresh memory
      (InputUpdateTrace.first_current mode (updateLayout mode layout) targetOld fresh false memory update)
  · exact DwordOperandTemplates.initial .bitAnd (updateStart mode layout+10) _ 0 memory
      (InputUpdateTrace.second_current mode (updateLayout mode layout) targetOld fresh false memory update)
  · exact DwordUnaryTemplates.initial .xorAtAccumulator _ targetOld memory
      (CursorImage.middle_current mode (InputUpdate.body (updateLayout mode layout)) targetOld memory
        (InputUpdate.body_current mode (updateLayout mode layout) targetOld fresh false memory update))

theorem all_states (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (intact : Listing8LiteralInput.Intact mode layout candidate ruleOld targetOld fresh state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    StringTemplateStates.Run mode (fun current => ∀ template∈templates mode layout,Decodes mode template current.principal.memory)
      (((Listing8LiteralComposition.program mode layout candidate ruleOld fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  DwordTemplateCollection.all_decodes mode _ _ state (initial mode layout candidate ruleOld targetOld fresh _ intact)
    (Listing8InputTemplateRegions.complete mode layout candidate ruleOld targetOld fresh capacity masks update outside
      state.principal entry intact cursor _ (owned_fields mode layout masks outside))

theorem mask_operand (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (memory : ByteMemory.Memory) (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask memory) :
    DwordCode.get memory (maskField mode layout)=oldMask := by
  have packet := ByteWindow.packet memory layout.start (Listing8InputMask.leading mode layout rule tape fresh)
    (LittleEndian.wordEncode 4 oldMask) (Listing8InputMask.trailing mode layout pending) current
  rw [Listing8InputMask.mask_position,LittleEndian.word_encode_length] at packet
  have restored := DwordCode.get_put memory (maskField mode layout) oldMask
  have written := ByteMemory.bytes_at_put memory (maskField mode layout) (LittleEndian.wordEncode 4 oldMask)
  rw [LittleEndian.word_encode_length] at written
  rw [DwordCode.get,DwordCode.put,written] at restored
  simpa only [DwordCode.get,packet] using restored

/-- Arbitrary original AND masks have the same fixed descriptors. The
temporary normalization is a memory equality proof, not a native reset step. -/
theorem mask_initial (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (memory : ByteMemory.Memory) (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask memory) :
    All (templates mode layout) memory := by
  have normalized := initial mode layout rule tape pending fresh _
    (Listing8InputMask.zero_intact mode layout rule tape pending fresh oldMask memory current)
  have back := store_all (templates mode layout) (DwordCode.put memory (maskField mode layout) 0)
    (maskField mode layout) (LittleEndian.wordEncode 4 oldMask) normalized
    (by rw [LittleEndian.word_encode_length];exact internal_fields mode layout _ (Or.inr (Or.inr (Or.inl rfl))))
  change All (templates mode layout) (DwordCode.put (DwordCode.put memory (maskField mode layout) 0) (maskField mode layout) oldMask) at back
  rw [DwordCode.put_overwrite,←mask_operand mode layout rule tape pending fresh oldMask memory current,DwordCode.put_get_back] at back
  exact back

theorem mask_templates (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    StringTemplateStates.Run mode (fun reached => All (templates mode layout) reached.principal.memory)
      (((Listing8LiteralComposition.program mode layout rule tape fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  DwordTemplateCollection.all_states mode _ _ state (mask_initial mode layout rule tape pending fresh oldMask _ current)
    (Listing8InputTemplateRegions.mask_complete mode layout rule tape pending fresh oldMask capacity masks update outside
      state.principal entry current cursor _ (owned_fields mode layout masks outside))

theorem mask_decodes (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    StringTemplateStates.Run mode (fun reached => ∀ template∈templates mode layout,Decodes mode template reached.principal.memory)
      (((Listing8LiteralComposition.program mode layout rule tape fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun reached all template member => decodes mode template reached.principal.memory (all template member))
    (mask_templates mode layout rule tape pending fresh oldMask capacity masks update outside state entry current cursor)

theorem at_prefix (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head)
    (before after : List (StringStack.Form mode))
    (cut : ((Listing8LiteralComposition.program mode layout rule tape fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)=before++after) :
    All (templates mode layout) (StringWrites.run mode before state).principal.memory ∧
    ∀ template∈templates mode layout,Decodes mode template (StringWrites.run mode before state).principal.memory := by
  have states := mask_templates mode layout rule tape pending fresh oldMask capacity masks update outside state entry current cursor
  rw [cut] at states
  have intact := StringTemplateStates.at_prefix mode _ before after state states
  exact ⟨intact,fun template member => decodes mode template _ (intact template member)⟩

end SmcTuring.Appendix.Listing8InputExecutableTemplates

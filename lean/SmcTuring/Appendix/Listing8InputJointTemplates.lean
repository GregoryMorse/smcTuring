module
public import SmcTuring.Native.MixedTemplateGeometry
public import SmcTuring.Appendix.Listing8InputFixedTemplates

public section
namespace SmcTuring.Appendix.Listing8InputJointTemplates
open Native Listing8LiteralInput

@[expose] def templateWindows (mode : Mode) (layout : Layout) : List (Nat × Nat) :=
  (Listing8InputExecutableTemplates.templates mode layout).map (fun template =>
    (DwordTemplateCollection.start template,DwordTemplateCollection.span template)) ++
  (Listing8InputFixedTemplates.entries mode layout).map (fun entry => (entry.pc,MixedFixedTemplates.span mode entry))
@[expose] def ValidWindow (mode : Mode) (window : Nat × Nat) (memory : ByteMemory.Memory) : Prop :=
  ∃ form : MixedDword.Form mode,
    StringStack.fetch mode memory window.1=some (StringStoreWrites.liftDword mode (StringMixed.canonical mode form)) ∧
    MixedDword.length mode form=window.2

theorem actual_x86 (layout : Layout) (rule tape fresh : Dword) :
    MixedTemplateGeometry.windows .x86 layout.start (Listing8LiteralComposition.program .x86 layout rule tape fresh)=
    [(layout.start,10),
     (layout.start+10,6),
     (layout.start+16,5),
     (layout.start+21,6),
     (layout.start+27,10),
     (layout.start+37,10),
     (layout.start+47,6),
     (layout.start+53,7),
     (layout.start+60,6),
     (layout.start+66,6),
     (layout.start+72,5),
     (layout.start+77,6),
     (layout.start+83,6),
     (layout.start+89,5),
     (layout.start+94,6),
     (layout.start+100,10),
     (layout.start+110,10),
     (layout.start+120,6),
     (layout.start+126,7),
     (layout.start+133,6)] := by
  simp [MixedTemplateGeometry.windows,Listing8LiteralComposition.program,prefixProgram,resetForm,ownerForm,DwordLayout.program,DwordLayout.first,DwordLayout.second,DwordLayout.third,DwordComparisonTail.program,DwordComparisonTail.form,DwordComparisonTail.raw,DwordComparisonTail.offset,DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,MixedDword.length,DwordCode.length,Listing8LiteralMaskTrace.program,DwordMixedSequence.program,distributionLayouts,Listing8MaskCopy.distributionLayouts,InputUpdate.program,InputUpdate.xorForm,InputUpdate.andForm,CursorLayout.program,CursorLayout.first,CursorLayout.middle,CursorLayout.last,MixedDword.exchange,copyLayout,tailLayout,updateLayout,InputUpdate.body,ownerPC,copyStart,distributionStart,updateStart,gap,DwordLayout.span,DwordLayout.storeSize,Mode.wordBytes,Nat.add_assoc]

theorem actual_x64 (layout : Layout) (rule tape fresh : Dword) :
    MixedTemplateGeometry.windows .x64 layout.start (Listing8LiteralComposition.program .x64 layout rule tape fresh)=
    [(layout.start,10),
     (layout.start+10,6),
     (layout.start+16,6),
     (layout.start+22,6),
     (layout.start+28,10),
     (layout.start+38,10),
     (layout.start+48,6),
     (layout.start+54,7),
     (layout.start+61,6),
     (layout.start+67,6),
     (layout.start+73,6),
     (layout.start+79,6),
     (layout.start+85,6),
     (layout.start+91,6),
     (layout.start+97,6),
     (layout.start+103,6),
     (layout.start+109,6),
     (layout.start+115,6),
     (layout.start+121,6),
     (layout.start+127,6),
     (layout.start+133,6),
     (layout.start+139,10),
     (layout.start+149,10),
     (layout.start+159,7),
     (layout.start+166,7),
     (layout.start+173,7)] := by
  simp [MixedTemplateGeometry.windows,Listing8LiteralComposition.program,prefixProgram,resetForm,ownerForm,DwordLayout.program,DwordLayout.first,DwordLayout.second,DwordLayout.third,DwordComparisonTail.program,DwordComparisonTail.form,DwordComparisonTail.raw,DwordComparisonTail.offset,DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,MixedDword.length,DwordCode.length,Listing8LiteralMaskTrace.program,DwordMixedSequence.program,distributionLayouts,Listing8MaskCopy.distributionLayouts,InputUpdate.program,InputUpdate.xorForm,InputUpdate.andForm,CursorLayout.program,CursorLayout.first,CursorLayout.middle,CursorLayout.last,MixedDword.exchange,copyLayout,tailLayout,updateLayout,InputUpdate.body,ownerPC,copyStart,distributionStart,updateStart,gap,DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc]

theorem templates_x86 (layout : Layout) :
    templateWindows .x86 layout=
    [(layout.start,10),
     (layout.start+27,10),
     (layout.start+37,10),
     (layout.start+47,6),
     (layout.start+53,7),
     (layout.start+60,6),
     (layout.start+100,10),
     (layout.start+110,10),
     (layout.start+126,7),
     (layout.start+10,6),
     (layout.start+16,5),
     (layout.start+21,6),
     (layout.start+66,6),
     (layout.start+72,5),
     (layout.start+77,6),
     (layout.start+83,6),
     (layout.start+89,5),
     (layout.start+94,6),
     (layout.start+120,6),
     (layout.start+133,6)] := by
  simp [templateWindows,Listing8InputExecutableTemplates.templates,Listing8InputFixedTemplates.entries,Listing8InputFixedTemplates.cursorEntries,MixedFixedTemplates.copyEntries,DwordTemplateCollection.start,DwordTemplateCollection.span,DwordUnaryTemplates.span,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,MixedFixedTemplates.span,MixedDword.encode_length,MixedDword.length,MixedDword.exchange,CursorLayout.first,CursorLayout.last,DwordCode.length,DwordLayout.first,DwordLayout.second,DwordLayout.third,distributionLayouts,Listing8MaskCopy.distributionLayouts,copyLayout,updateLayout,InputUpdate.body,ownerPC,copyStart,distributionStart,updateStart,gap,DwordLayout.span,DwordLayout.storeSize,DwordLayout.secondPC,DwordLayout.thirdPC,CursorLayout.lastPC,CursorLayout.middlePC,CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,Mode.wordBytes,Nat.add_assoc]

theorem templates_x64 (layout : Layout) :
    templateWindows .x64 layout=
    [(layout.start,10),
     (layout.start+28,10),
     (layout.start+38,10),
     (layout.start+48,6),
     (layout.start+54,7),
     (layout.start+61,6),
     (layout.start+139,10),
     (layout.start+149,10),
     (layout.start+166,7),
     (layout.start+10,6),
     (layout.start+16,6),
     (layout.start+22,6),
     (layout.start+67,6),
     (layout.start+73,6),
     (layout.start+79,6),
     (layout.start+85,6),
     (layout.start+91,6),
     (layout.start+97,6),
     (layout.start+103,6),
     (layout.start+109,6),
     (layout.start+115,6),
     (layout.start+121,6),
     (layout.start+127,6),
     (layout.start+133,6),
     (layout.start+159,7),
     (layout.start+173,7)] := by
  simp [templateWindows,Listing8InputExecutableTemplates.templates,Listing8InputFixedTemplates.entries,Listing8InputFixedTemplates.cursorEntries,MixedFixedTemplates.copyEntries,DwordTemplateCollection.start,DwordTemplateCollection.span,DwordUnaryTemplates.span,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,MixedFixedTemplates.span,MixedDword.encode_length,MixedDword.length,MixedDword.exchange,CursorLayout.first,CursorLayout.last,DwordCode.length,DwordLayout.first,DwordLayout.second,DwordLayout.third,distributionLayouts,Listing8MaskCopy.distributionLayouts,copyLayout,updateLayout,InputUpdate.body,ownerPC,copyStart,distributionStart,updateStart,gap,DwordLayout.span,DwordLayout.storeSize,DwordLayout.secondPC,DwordLayout.thirdPC,CursorLayout.lastPC,CursorLayout.middlePC,CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,Mode.wordBytes,Nat.add_assoc]

/-- Every original static packet window belongs to one of the two proved
collections, using the exact literal ordered helper expansion in both modes. -/
theorem coverage (mode : Mode) (layout : Layout) (rule tape fresh : Dword) (window : Nat × Nat)
    (member : window∈MixedTemplateGeometry.windows mode layout.start
      (Listing8LiteralComposition.program mode layout rule tape fresh)) :
    window∈templateWindows mode layout := by
  cases mode with
  | x86 =>
    rw [actual_x86] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [templates_x86]
  | x64 =>
    rw [actual_x64] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [templates_x64]

theorem valid_windows (mode : Mode) (layout : Layout) (memory : ByteMemory.Memory)
    (arithmetic : DwordTemplateCollection.All (Listing8InputExecutableTemplates.templates mode layout) memory)
    (fixed : MixedFixedTemplates.All mode (Listing8InputFixedTemplates.entries mode layout) memory)
    (window : Nat × Nat) (member : window∈templateWindows mode layout) : ValidWindow mode window memory := by
  simp only [templateWindows,List.mem_append] at member
  rcases member with a | b
  · rcases List.mem_map.mp a with ⟨template,inside,rfl⟩
    have fetched := DwordTemplateCollection.decodes mode template memory (arithmetic template inside)
    cases template with
    | binary kind pc =>
      refine ⟨.arithmetic (DwordOperandTemplates.form kind (DwordCode.get memory (pc+2)) (DwordCode.get memory (pc+6))),fetched,?_⟩
      have length := DwordOperandTemplates.length kind (DwordCode.get memory (pc+2)) (DwordCode.get memory (pc+6))
      simpa only [MixedDword.length,DwordArithmetic.encode_length,DwordTemplateCollection.span] using length
    | unary kind pc =>
      refine ⟨.arithmetic (DwordUnaryTemplates.form kind (DwordCode.get memory (DwordUnaryTemplates.field kind pc))),fetched,?_⟩
      have length := DwordUnaryTemplates.length kind (DwordCode.get memory (DwordUnaryTemplates.field kind pc))
      simpa only [MixedDword.length,DwordArithmetic.encode_length,DwordTemplateCollection.span] using length
  · rcases List.mem_map.mp b with ⟨entry,inside,rfl⟩
    exact ⟨entry.form,MixedFixedTemplates.decodes mode entry memory (fixed entry inside),(MixedDword.encode_length mode entry.form).symm⟩

theorem all_states (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    StringTemplateStates.Run mode (fun reached =>
      DwordTemplateCollection.All (Listing8InputExecutableTemplates.templates mode layout) reached.principal.memory ∧
      MixedFixedTemplates.All mode (Listing8InputFixedTemplates.entries mode layout) reached.principal.memory)
      (((Listing8LiteralComposition.program mode layout rule tape fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  MixedTemplateGeometry.conjunction mode _ _ _ state
    (Listing8InputExecutableTemplates.mask_templates mode layout rule tape pending fresh oldMask capacity masks update outside state entry current cursor)
    (Listing8InputFixedTemplates.all_states mode layout rule tape pending fresh oldMask capacity masks update outside state entry current cursor)

/-- At every actual reached input-phase boundary, every original instruction
window decodes from that same memory with its exact original extent. -/
theorem all_windows (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    StringTemplateStates.Run mode (fun reached =>
      ∀ window∈MixedTemplateGeometry.windows mode layout.start (Listing8LiteralComposition.program mode layout rule tape fresh),
        ValidWindow mode window reached.principal.memory)
      (((Listing8LiteralComposition.program mode layout rule tape fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun reached both window member => valid_windows mode layout reached.principal.memory both.1 both.2 window
      (coverage mode layout rule tape fresh window member))
    (all_states mode layout rule tape pending fresh oldMask capacity masks update outside state entry current cursor)

theorem at_prefix (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head)
    (before after : List (StringStack.Form mode))
    (cut : ((Listing8LiteralComposition.program mode layout rule tape fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)=before++after) :
    ∀ window∈MixedTemplateGeometry.windows mode layout.start (Listing8LiteralComposition.program mode layout rule tape fresh),
      ValidWindow mode window (StringWrites.run mode before state).principal.memory := by
  have states := all_windows mode layout rule tape pending fresh oldMask capacity masks update outside state entry current cursor
  rw [cut] at states
  exact StringTemplateStates.at_prefix mode _ before after state states

end SmcTuring.Appendix.Listing8InputJointTemplates

module
public import SmcTuring.Appendix.Listing8RetargetPointerFields
public import SmcTuring.Appendix.Listing8MacroOwnerFrames

public section
namespace SmcTuring.Appendix.Listing8MacroPointerFrames
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def Allowed (mode : Mode) (l : Layout) (address count : Nat) : Prop :=
  patchStart mode l≤address ∨
    (address=StringCodec.sourceField mode (secondStart mode l) ∧ count≤mode.wordBytes)
@[expose] def Property (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) : Prop :=
  StringMacroTemplates.Intact mode (nodeParams mode l) memory ∧
    StringMacroTemplates.Intact mode (transitionParams mode l) memory

theorem word_fields (mode : Mode) (l : Layout) :
    Allowed mode l (Listing8PointerCopies.word mode l).source mode.wordBytes ∧
      Allowed mode l (Listing8PointerCopies.word mode l).destination mode.wordBytes := by
  constructor
  · left
    cases mode <;> simp only [Listing8PointerCopies.word,pointerField,transitionParams,patchLayout,
      Listing8ModeOffsets.transitionEntry,Listing8ModeOffsets.nodeEntry,nodeSpan,ReaderImage.labelOffset] <;> omega
  · exact Or.inr ⟨rfl,Nat.le_refl _⟩

theorem dword_fields (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8PointerCopies.Bounds mode l t) :
    ∀ lay∈Listing8PointerCopies.layouts mode l t,Allowed mode l lay.source 4 ∧ Allowed mode l lay.destination 4 := by
  intro lay member
  have ending:=(coordinates mode l).2.2
  have size:=(Listing8PointerCopies.sizes mode l t).2.1
  have destination:=Listing8PointerCopies.destination_after mode l t bounds lay member
  exact ⟨Or.inl (Listing8PointerCopies.source_bounds mode l t lay member).1,Or.inl (by omega)⟩

theorem regions (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8PointerCopies.Bounds mode l t)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (codeEnd mode l)) :
    StringStoreRegions.Run mode (Allowed mode l)
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)) state := by
  have fields:=word_fields mode l
  have first:=CopyStoreRegions.word mode _ (Listing8PointerCopies.word mode l) bounds.wordValid state entry fields.1 fields.2
  have next : (StringDwordCopy.wordFinish mode (Listing8PointerCopies.word mode l) state).principal.pc=
      Arithmetic.encodeNat mode (Listing8PointerCopies.dwordStart mode l) := by
    change (ConversionEffects.finish mode (Listing8PointerCopies.word mode l) state.principal).pc=_
    rw [ConversionEffects.effect mode (Listing8PointerCopies.word mode l) bounds.wordValid state.principal entry];rfl
  have last:=CopyStoreRegions.sequence mode _ (Listing8PointerCopies.layouts mode l t) _ (Listing8PointerCopies.chain mode l t)
    bounds.dwordValid (dword_fields mode l t bounds) _ next
  rw [Listing8PointerCopies.program,List.map_append,StringStoreRegions.append,StringSequenceWrites.word_run]
  exact ⟨first,last⟩

theorem store (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (initial : Property mode l memory) (allowed : Allowed mode l address packet.length) :
    Property mode l (ByteMemory.putBytes memory address packet) := by
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  rcases allowed with after | ⟨rfl,small⟩
  · exact ⟨StringMacroTemplates.frame mode _ memory _ packet initial.1 (Or.inr (second.trans after)),
      StringMacroTemplates.frame mode _ memory _ packet initial.2 (Or.inr after)⟩
  · have fieldAfter : secondStart mode l≤StringCodec.sourceField mode (secondStart mode l) := by
      unfold StringCodec.sourceField;omega
    exact ⟨StringMacroTemplates.frame mode _ memory _ packet initial.1 (Or.inr fieldAfter),
      StringMacroTemplates.operand_store mode _ memory _ packet initial.2 (Or.inl ⟨Nat.le_refl _,by change StringCodec.sourceField mode (secondStart mode l)+packet.length≤StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes;omega⟩)⟩

theorem all_states (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8PointerCopies.Bounds mode l t)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (codeEnd mode l))
    (initial : Property mode l state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Property mode l reached.principal.memory)
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)) state :=
  StringStoreTemplateRuns.preserve mode (Allowed mode l) (Property mode l) _ state initial
    (store mode l) (regions mode l t bounds state entry)

theorem all_decodes (mode : Mode) (l : Layout) (t : Targets) (bounds : Listing8PointerCopies.Bounds mode l t)
    (resources : Resources mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (codeEnd mode l))
    (initial : Property mode l state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      StringEncodedTemplates.Decodes mode (nodeParams mode l) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (transitionParams mode l) reached.principal.memory)
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ _ (fun reached both =>
    ⟨StringEncodedTemplates.macro_decodes mode _ reached.principal.memory resources.node.sizeFits both.1,
      StringEncodedTemplates.macro_decodes mode _ reached.principal.memory resources.transition.sizeFits both.2⟩)
    (all_states mode l t bounds state entry initial)

end SmcTuring.Appendix.Listing8MacroPointerFrames

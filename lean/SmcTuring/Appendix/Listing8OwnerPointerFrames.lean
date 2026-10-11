module
public import SmcTuring.Appendix.Listing8MacroPointerFrames
public import SmcTuring.Appendix.Listing8CopiedOwnerCatalog
public import SmcTuring.Appendix.Listing8GlobalPointerRegions

public section
namespace SmcTuring.Appendix.Listing8OwnerPointerFrames
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8OwnerTemplateCollection
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def Compatible (mode : Mode) (template : Template mode) (address count : Nat) : Prop :=
  (field mode template≤address ∧ address+count≤field mode template+width mode template) ∨
    (address+count≤start mode template ∨ start mode template+span mode template≤address)
@[expose] def CompatibleAll (mode : Mode) (templates : List (Template mode)) (address count : Nat) : Prop :=
  ∀ template∈templates,Compatible mode template address count

theorem store (mode : Mode) (templates : List (Template mode)) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List LittleEndian.Byte) (initial : All mode templates memory)
    (compatible : CompatibleAll mode templates address packet.length) :
    All mode templates (ByteMemory.putBytes memory address packet) := by
  intro template member
  rcases compatible template member with operand | outside
  · exact operand_store mode template memory (initial template member) ⟨address,packet⟩ operand
  · exact frame mode template memory (initial template member) ⟨address,packet⟩ outside

theorem ranges (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (template : Template mode) (member : template∈Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))) :
    (patchStart mode l≤start mode template ∧ start mode template+span mode template≤codeEnd mode l) ∨
      Listing8FullTableImage.start mode origin≤start mode template := by
  have original:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  simp only [Listing8CopiedOwnerCatalog.catalog,Listing8OwnerImage.owners,Listing8CopiedOwnerCatalog.entries,
    List.flatMap_cons,List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | rfl | rfl | rfl | (rfl | rfl)
  all_goals cases mode
  all_goals simp only [start,span,nodeParams,transitionParams,patchLayout,Listing8ModeOffsets.nodeEntry,
    Listing8ModeOffsets.transitionEntry,codeEnd,Listing8ModeOffsets.endPC,backEntry,forwardEntry,stateEntry,
    currentEntry,newEntry,directionEntry,pointerSpan,nodeSpan,transitionSpan,ReaderImage.totalSize]
  all_goals omega

theorem word_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    CompatibleAll mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)))
      (Listing8PointerCopies.word mode l).source mode.wordBytes ∧
    CompatibleAll mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)))
      (Listing8PointerCopies.word mode l).destination mode.wordBytes := by
  have original:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have copied:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  have nodeAfter : patchStart mode l+40+nodeSpan mode+transitionSpan mode≤l.sourceNode := by
    change codeEnd mode l≤l.sourceNode
    omega
  have ruleAfter : patchStart mode l+40+nodeSpan mode+transitionSpan mode≤l.sourceTransition := by
    change codeEnd mode l≤l.sourceTransition
    omega
  constructor
  · intro template member
    simp only [Listing8CopiedOwnerCatalog.catalog,Listing8OwnerImage.owners,Listing8CopiedOwnerCatalog.entries,
      List.flatMap_cons,List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | rfl | rfl | rfl | (rfl | rfl)
    all_goals cases mode
    all_goals simp only [Compatible,field,width,start,span,Listing8PointerCopies.word,pointerField,nodeParams,transitionParams,
      patchLayout,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,
      backEntry,forwardEntry,stateEntry,currentEntry,newEntry,directionEntry,pointerSpan,nodeSpan,transitionSpan,
      ReaderImage.totalSize,ReaderImage.labelOffset,Mode.wordBytes]
    all_goals simp only [nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize] at nodeAfter ruleAfter
    all_goals omega
  · intro template member
    have bound:=ranges mode origin l t g node rule ctx template member
    have cursor:=Listing8PointerCopies.cursor_before_patch mode l
    change Compatible mode template _ _
    right;left
    rcases bound with localBounds | later
    · exact cursor.trans localBounds.1
    · have main:=copied.2
      have endBound:=(coordinates mode l).2.2
      omega

theorem dword_sources (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (lay : DwordLayout.Layout) (inside : lay∈Listing8PointerCopies.layouts mode l t) :
    CompatibleAll mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))) lay.source 4 := by
  have original:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have copied:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  have nodeAfter : patchStart mode l+40+nodeSpan mode+transitionSpan mode≤l.sourceNode := by
    change codeEnd mode l≤l.sourceNode
    omega
  have ruleAfter : patchStart mode l+40+nodeSpan mode+transitionSpan mode≤l.sourceTransition := by
    change codeEnd mode l≤l.sourceTransition
    omega
  cases mode <;> simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at inside
  · rcases inside with rfl | rfl | rfl
    all_goals intro template member
    all_goals simp only [Listing8CopiedOwnerCatalog.catalog,Listing8OwnerImage.owners,Listing8CopiedOwnerCatalog.entries,
      List.flatMap_cons,List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | rfl | rfl | rfl | (rfl | rfl)
    all_goals simp only [Compatible,field,width,start,span,pointerField,nodeParams,transitionParams,patchLayout,
      Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,backEntry,forwardEntry,
      stateEntry,currentEntry,newEntry,directionEntry,pointerSpan,nodeSpan,transitionSpan,ReaderImage.totalSize,ReaderImage.labelOffset,Mode.wordBytes]
    all_goals simp only [nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize] at nodeAfter ruleAfter
    all_goals omega
  · rcases inside with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals intro template member
    all_goals simp only [Listing8CopiedOwnerCatalog.catalog,Listing8OwnerImage.owners,Listing8CopiedOwnerCatalog.entries,
      List.flatMap_cons,List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | rfl | rfl | rfl | (rfl | rfl)
    all_goals simp only [Compatible,field,width,start,span,pointerField,nodeParams,transitionParams,patchLayout,
      Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,backEntry,forwardEntry,
      stateEntry,currentEntry,newEntry,directionEntry,pointerSpan,nodeSpan,transitionSpan,ReaderImage.totalSize,ReaderImage.labelOffset,Mode.wordBytes]
    all_goals simp only [nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize] at nodeAfter ruleAfter
    all_goals omega

theorem dword_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ lay∈Listing8PointerCopies.layouts mode l t,
      CompatibleAll mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))) lay.source 4 ∧
      CompatibleAll mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))) lay.destination 4 := by
  intro lay member
  refine ⟨dword_sources mode origin l t g node rule ctx lay member,?_⟩
  intro template inside
  have bounds:=ranges mode origin l t g node rule ctx template inside
  have lower:=Listing8PointerCopies.destination_after mode l t ctx.copies lay member
  have size:=(Listing8PointerCopies.sizes mode l t).2.1
  have upper:=(Listing8GlobalPointerRegions.dwords mode origin l t g node rule ctx lay member).2.2
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  right
  rcases bounds with before | after
  · right;omega
  · left;omega

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (codeEnd mode l)) :
    StringStoreRegions.Run mode (CompatibleAll mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))))
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)) state := by
  have fields:=word_fields mode origin l t g node rule ctx
  have first:=CopyStoreRegions.word mode _ (Listing8PointerCopies.word mode l) ctx.copies.wordValid state entry fields.1 fields.2
  have next : (StringDwordCopy.wordFinish mode (Listing8PointerCopies.word mode l) state).principal.pc=
      Arithmetic.encodeNat mode (Listing8PointerCopies.dwordStart mode l) := by
    change (ConversionEffects.finish mode (Listing8PointerCopies.word mode l) state.principal).pc=_
    rw [ConversionEffects.effect mode (Listing8PointerCopies.word mode l) ctx.copies.wordValid state.principal entry];rfl
  have last:=CopyStoreRegions.sequence mode _ (Listing8PointerCopies.layouts mode l t) _ (Listing8PointerCopies.chain mode l t)
    ctx.copies.dwordValid (dword_fields mode origin l t g node rule ctx) _ next
  rw [Listing8PointerCopies.program,List.map_append,StringStoreRegions.append,StringSequenceWrites.word_run]
  exact ⟨first,last⟩

theorem all_states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (codeEnd mode l))
    (initial : All mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => All mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))) reached.principal.memory)
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)) state :=
  StringStoreTemplateRuns.preserve mode _ _ _ state initial (store mode _)
    (regions mode origin l t g node rule ctx state entry)

end SmcTuring.Appendix.Listing8OwnerPointerFrames

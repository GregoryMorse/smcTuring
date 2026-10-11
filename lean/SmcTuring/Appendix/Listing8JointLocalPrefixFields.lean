module
public import SmcTuring.Appendix.Listing8JointLocalContinuation

public section
namespace SmcTuring.Appendix.Listing8JointLocalPrefixFields
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8JointLocalCatalog
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000

theorem exterior (mode : Mode) (l : Layout) (sentinel begin address count : Nat)
    (outside : address+count≤l.input.start ∨ Listing8FailureLayout.callPC mode (failure mode l sentinel begin)+5≤address) :
    Compatible mode l sentinel begin address count := by
  have order:=ordering mode l sentinel begin
  apply Listing8JointLocalCatalog.exterior
  · rcases outside with early | late
    · exact Or.inl early
    · exact Or.inr (order.2.2.2.trans late)
  · rcases outside with early | late
    · exact Or.inl (early.trans (order.1.trans (order.2.1.trans order.2.2.1)))
    · exact Or.inr (Or.inl late)

theorem fresh_arithmetic (mode : Mode) (layout : Listing8LiteralInput.Layout) :
    DwordTemplateCollection.CompatibleAll (Listing8InputExecutableTemplates.templates mode layout)
      (Listing8LiteralInput.updateStart mode layout+6) 4 := by
  intro template member
  simp only [Listing8InputExecutableTemplates.templates,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases mode
  all_goals simp [DwordTemplateCollection.Compatible,DwordTemplateCollection.start,DwordTemplateCollection.span,
    DwordTemplateCollection.field,DwordTemplateCollection.width,DwordUnaryTemplates.span,DwordUnaryTemplates.field,
    DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,Listing8LiteralInput.ownerPC,Listing8LiteralInput.copyStart,
    Listing8LiteralInput.updateStart,Listing8LiteralInput.distributionStart,Listing8LiteralInput.gap,DwordLayout.span,
    DwordLayout.storeSize,Listing8LiteralInput.updateLayout,InputUpdate.body,CursorLayout.middlePC,CursorLayout.exchangeSize]
  all_goals omega

theorem fresh_fixed (mode : Mode) (layout : Listing8LiteralInput.Layout) :
    MixedFixedTemplates.OutsideAll mode (Listing8InputFixedTemplates.entries mode layout)
      (Listing8LiteralInput.updateStart mode layout+6) 4 := by
  intro entry member
  simp only [Listing8InputFixedTemplates.entries,List.mem_append] at member
  rcases member with (first | distribution) | cursor
  · have range:=Listing8InputFixedTemplates.first_copy_bounds mode layout entry first
    right
    have before : Listing8LiteralInput.ownerPC mode layout≤Listing8LiteralInput.updateStart mode layout := by
      unfold Listing8LiteralInput.updateStart Listing8LiteralInput.distributionStart;omega
    exact range.2.trans (by omega)
  · have range:=Listing8InputFixedTemplates.distribution_bounds mode layout entry distribution
    exact Or.inr (range.2.trans (by omega))
  · simp only [Listing8InputFixedTemplates.cursorEntries,List.mem_cons,List.not_mem_nil,or_false] at cursor
    rcases cursor with rfl | rfl
    all_goals left
    all_goals simp [Listing8LiteralInput.updateLayout,InputUpdate.body,CursorLayout.lastPC,CursorLayout.middlePC,
      CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix]
    all_goals omega

/-- Operand-compatible input stores preserve every later executable header. -/
theorem before_head (mode : Mode) (l : Layout) (sentinel begin address : Nat)
    (arithmetic : DwordTemplateCollection.CompatibleAll (Listing8InputExecutableTemplates.templates mode l.input) address 4)
    (fixed : MixedFixedTemplates.OutsideAll mode (Listing8InputFixedTemplates.entries mode l.input) address 4)
    (upper : address+4≤(head mode l).start) : Compatible mode l sentinel begin address 4 := by
  have order:=ordering mode l sentinel begin
  have stateBefore:=upper.trans order.2.1
  exact ⟨arithmetic,fixed,Listing8DirectionTemplateFields.compatible mode _ address (Or.inl upper),
    Listing8DirectionTemplateFields.fixed_frames mode _ address (Or.inl upper),
    Listing8DirectionTemplateFields.xor_frames mode _ address (Or.inl upper),
    Listing8StateTemplateFields.compatible mode _ address (Or.inl stateBefore),
    Listing8StateTemplateFields.frames mode _ address (Or.inl stateBefore),Or.inl (stateBefore.trans order.2.2.1)⟩

theorem input_fields (mode : Mode) (l : Layout) (sentinel begin address : Nat)
    (chosen : address=Listing8LiteralInput.scalarField mode l.input ∨ address=Listing8LiteralInput.sourceField mode l.input ∨
      address=Listing8LiteralInput.updateStart mode l.input+6) : Compatible mode l sentinel begin address 4 := by
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have coords:=Listing8LiteralInput.positions mode l.input
  rcases chosen with rfl | rfl | rfl
  · exact before_head mode l sentinel begin _
      (Listing8InputExecutableTemplates.internal_fields mode l.input _ (Or.inl rfl))
      (Listing8InputFixedTemplates.internal_fields mode l.input _ (Or.inl rfl)) scalar.2.1
  · exact before_head mode l sentinel begin _
      (Listing8InputExecutableTemplates.internal_fields mode l.input _ (Or.inr (Or.inl rfl)))
      (Listing8InputFixedTemplates.internal_fields mode l.input _ (Or.inr (Or.inl rfl))) source.2
  · apply before_head mode l sentinel begin _ (fresh_arithmetic mode l.input) (fresh_fixed mode l.input)
    change Listing8LiteralInput.updateStart mode l.input+6+4≤Listing8LiteralInput.endPC mode l.input
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega

structure MacroPlacement (mode : Mode) (l : Layout) (sentinel begin : Nat) (p : StringMacroLayout.Params) : Prop where
  codeBefore : StringMacroLayout.endpoint mode p≤l.input.start
  sourceAfter : Listing8FailureLayout.callPC mode (failure mode l sentinel begin)+5≤p.source
  destinationBefore : p.destination+max p.size mode.wordBytes≤l.input.start

theorem macro_packet (mode : Mode) (l : Layout) (sentinel begin : Nat) (p : StringMacroLayout.Params)
    (placed : MacroPlacement mode l sentinel begin p) (packet : StringWrites.Packet)
    (inside : StringPacketRegions.Allowed mode p packet) :
    Compatible mode l sentinel begin packet.address packet.bytes.length := by
  have fields:=StringMacroLayout.field_coordinates mode p
  rcases inside with sourceField | destinationField | source | destination
  · apply exterior;left
    unfold StringPacketRegions.Within at sourceField
    have before:=placed.codeBefore
    omega
  · apply exterior;left
    unfold StringPacketRegions.Within at destinationField
    have before:=placed.codeBefore
    omega
  · exact exterior mode l sentinel begin _ _ (Or.inr (placed.sourceAfter.trans source.1))
  · apply exterior;left
    exact destination.2.trans placed.destinationBefore

theorem macro_regions (mode : Mode) (l : Layout) (sentinel begin : Nat) (p : StringMacroLayout.Params)
    (placed : MacroPlacement mode l sentinel begin p) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode) (regions : StringPacketRegions.Run mode p forms state) :
    StringStoreRegions.Run mode (Compatible mode l sentinel begin) forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih => exact ⟨macro_packet mode l sentinel begin p placed _ regions.1,ih _ regions.2⟩

theorem call_before_table (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing8FailureLayout.callPC mode (failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5≤
      Listing8FullTableImage.start mode origin := by
  have geometry:=Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx
  have order:=Listing8GlobalControlLayout.ordered mode origin
  have callAt:=geometry.callAt
  change Listing8FailureLayout.callPC mode (failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=
    Listing8JumpLayout.callPC mode origin at callAt
  omega

theorem copy_placements (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    MacroPlacement mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (nodeParams mode l) ∧
    MacroPlacement mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (transitionParams mode l) := by
  have before:=ctx.resources.inputAfter
  have late:=call_before_table mode origin l t g node rule ctx
  have originals:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have coords:=coordinates mode l
  have dest:=destinations mode l
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  have word:=Listing8CopyWriteBounds.spans mode
  constructor
  · refine ⟨?_,late.trans originals.1,?_⟩
    · change secondStart mode l≤l.input.start;omega
    · change (nodeParams mode l).destination+max (nodeSpan mode) mode.wordBytes≤l.input.start
      rw [Nat.max_eq_left word.1];omega
  · refine ⟨?_,late.trans originals.2,?_⟩
    · change patchStart mode l≤l.input.start;omega
    · change (transitionParams mode l).destination+max (transitionSpan mode) mode.wordBytes≤l.input.start
      rw [Nat.max_eq_left word.2];omega


theorem pointer_self (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (source copied : Nat) (value : Word mode)
    (member : Listing8OwnerSequence.Owner.pointer source copied value∈Listing8OwnerImage.owners mode l (values mode origin g node rule)) :
    Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
      (Listing8CopiedPointer.selfField mode source copied) mode.wordBytes := by
  have copiedMember : copied∈Listing8OwnerImage.pointerPositions mode l := by
    simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h | h <;> cases h
    all_goals simp [Listing8OwnerImage.pointerPositions]
  have originals:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have late:=call_before_table mode origin l t g node rule ctx
  have sourceLater : Listing8FullTableImage.start mode origin≤source := by
    simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h | h <;> cases h
    all_goals first | exact originals.2 |
      (simp only [backEntry,forwardEntry,stateEntry,directionEntry,newEntry,currentEntry,pointerSpan,ReaderImage.totalSize];omega)
  cases mode
  · apply exterior;right
    simp only [Listing8CopiedPointer.selfField,Listing8CopiedPointer.origin,pointerField,ite_true]
    have lower:=late.trans sourceLater
    omega
  · apply exterior;left
    have range:=Listing8OwnerImage.pointer_bounds .x64 l copied copiedMember
    have before:=ctx.resources.inputAfter
    simp only [Listing8CopiedPointer.selfField,Listing8CopiedPointer.origin,pointerField,reduceCtorEq,ite_false,Mode.wordBytes,
      pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset] at range ⊢
    omega

theorem pointer_targets (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (word : Word mode) (member : word∈[(values mode origin g node rule).back,(values mode origin g node rule).forward,
      (values mode origin g node rule).next,(values mode origin g node rule).newState]) :
    Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) word.toNat mode.wordBytes := by
  have region : StringWrites.WordOwned mode (Listing8FullTableImage.start mode origin)
      (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) word := by
    simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Listing8LateGraphFieldBounds.node_word mode origin g (g.tape node).back ctx.native
    · exact Listing8LateGraphFieldBounds.node_word mode origin g (g.tape node).forward ctx.native
    · exact Listing8LateGraphFieldBounds.next_word mode origin g rule ctx.native
    · exact Listing8LateGraphFieldBounds.state_word mode origin g (g.rules rule).destination ctx.native
  exact exterior mode l _ _ _ _ (Or.inr ((call_before_table mode origin l t g node rule ctx).trans region.1))

theorem owner_placements (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ owner∈Listing8OwnerImage.owners mode l (values mode origin g node rule),
      Listing8OwnerStoreRegions.Placement mode (Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) owner := by
  intro owner member
  simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pointer_self mode origin l t g node rule ctx _ _ (values mode origin g node rule).back (by simp [Listing8OwnerImage.owners]),
      pointer_targets mode origin l t g node rule ctx _ (by simp)⟩
  · exact ⟨pointer_self mode origin l t g node rule ctx _ _ (values mode origin g node rule).forward (by simp [Listing8OwnerImage.owners]),
      pointer_targets mode origin l t g node rule ctx _ (by simp)⟩
  · exact ⟨pointer_self mode origin l t g node rule ctx _ _ (values mode origin g node rule).next (by simp [Listing8OwnerImage.owners]),
      pointer_targets mode origin l t g node rule ctx _ (by simp)⟩
  · exact input_fields mode l _ _ _ (Or.inl rfl)
  · exact input_fields mode l _ _ _ (Or.inr (Or.inr rfl))
  · apply head_slot mode origin l t g node rule ctx
    rw [ctx.body.state.head.direction]
    simp [headSlots]
  · exact ⟨pointer_self mode origin l t g node rule ctx _ _ (values mode origin g node rule).newState (by simp [Listing8OwnerImage.owners]),
      pointer_targets mode origin l t g node rule ctx _ (by simp)⟩


@[expose] def HeadPointerField (mode : Mode) (l : Layout) (address : Nat) : Prop :=
  address=Listing8DirectionLayout.backPC mode (head mode l)+6 ∨
  address=Listing8DirectionLayout.forwardPC mode (head mode l)+6 ∨
  (mode=.x64 ∧ address=Listing8DirectionLayout.backPC mode (head mode l)+16) ∨
  (mode=.x64 ∧ address=Listing8DirectionLayout.forwardPC mode (head mode l)+16)

theorem head_pointer_arithmetic (mode : Mode) (l : Layout) (address : Nat) (chosen : HeadPointerField mode l address) :
    DwordTemplateCollection.CompatibleAll (Listing8DirectionTemplateFields.templates mode (head mode l)) address 4 := by
  intro template member
  cases mode
  all_goals simp only [HeadPointerField,reduceCtorEq,true_and,false_and,or_false] at chosen
  all_goals rcases chosen with rfl | rfl | rfl | rfl
  all_goals simp only [Listing8DirectionTemplateFields.templates,Listing8DirectionTemplateFields.sites,
    Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.masks,Listing8DirectionLayout.heads,Listing8DirectionLayout.group,
    List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.Compatible,DwordTemplateCollection.start,
    DwordTemplateCollection.span,DwordTemplateCollection.field,DwordTemplateCollection.width,DwordUnaryTemplates.field,
    DwordUnaryTemplates.span,DwordUnaryTemplates.header,DwordUnaryTemplates.trailer,
    Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
    Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
    Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,
    Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize]

theorem head_pointer_field (mode : Mode) (l : Layout) (sentinel begin address : Nat)
    (chosen : HeadPointerField mode l address) : Compatible mode l sentinel begin address 4 := by
  have coords:=Listing8DirectionLayout.positions mode (head mode l)
  have placed : (head mode l).start≤address ∧ Listing8DirectionLayout.backPC mode (head mode l)≤address ∧
      address+4≤Listing8DirectionLayout.selectionEnd mode (head mode l) := by
    cases mode
    all_goals simp only [HeadPointerField,reduceCtorEq,true_and,false_and,or_false] at chosen
    all_goals rcases chosen with rfl | rfl | rfl | rfl
    all_goals simp only [reduceCtorEq,ite_true,ite_false] at coords
    all_goals omega
  have order:=ordering mode l sentinel begin
  have upper : address+4≤(transition mode l).start := by
    change address+4≤Listing8DirectionLayout.endPC mode (head mode l)
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  refine ⟨Listing8InputExecutableTemplates.exterior mode l.input address 4 (Or.inr placed.1),
    Listing8InputFixedTemplates.exterior mode l.input address 4 (Or.inr placed.1),
    head_pointer_arithmetic mode l address chosen,?_,?_,
    Listing8StateTemplateFields.compatible mode _ address (Or.inl upper),
    Listing8StateTemplateFields.frames mode _ address (Or.inl upper),Or.inl (upper.trans order.2.2.1)⟩
  · intro entry member
    exact Or.inr ((Listing8DirectionTemplateFields.fixed_bounds mode _ entry member).2.trans placed.2.1)
  · intro helper member
    cases mode
    · simp only [Listing8HeadTailBounds.xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl
      exact Or.inl placed.2.2
    · simp only [Listing8HeadTailBounds.xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact Or.inl placed.2.2
      · left
        change address+4≤Listing8DirectionLayout.selectionEnd .x64 (head .x64 l)+18
        have bound:=placed.2.2
        omega

@[expose] def StatePointerField (mode : Mode) (l : Layout) (address : Nat) : Prop :=
  address=Listing8StateLayout.newPC mode (transition mode l)+6 ∨
  (mode=.x64 ∧ address=Listing8StateLayout.newPC mode (transition mode l)+16)

theorem state_pointer_field (mode : Mode) (l : Layout) (sentinel begin address : Nat)
    (chosen : StatePointerField mode l address) : Compatible mode l sentinel begin address 4 := by
  have coords:=Listing8StateLayout.positions mode (transition mode l)
  have placed : (transition mode l).start≤address ∧ Listing8StateLayout.newPC mode (transition mode l)≤address ∧
      address+4≤(failure mode l sentinel begin).start := by
    change _ ∧ _ ∧ address+4≤Listing8StateLayout.endPC mode (transition mode l)
    cases mode
    all_goals simp only [StatePointerField,reduceCtorEq,true_and,false_and,or_false] at chosen
    all_goals rcases chosen with rfl | rfl
    all_goals simp only [reduceCtorEq,ite_true,ite_false] at coords
    all_goals omega
  have order:=ordering mode l sentinel begin
  have heads:=Listing8DirectionLayout.positions mode (head mode l)
  refine ⟨Listing8InputExecutableTemplates.exterior mode l.input address 4 (Or.inr (order.2.1.trans placed.1)),
    Listing8InputFixedTemplates.exterior mode l.input address 4 (Or.inr (order.2.1.trans placed.1)),?_,?_,?_,?_,?_,Or.inl placed.2.2⟩
  · intro template member
    exact Or.inr (Or.inr ((Listing8DirectionTemplateFields.template_bounds mode _ template member).2.trans placed.1))
  · intro entry member
    have bound:=Listing8DirectionTemplateFields.fixed_bounds mode (head mode l) entry member
    right
    have lower : Listing8DirectionLayout.endPC mode (head mode l)≤address := placed.1
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at heads <;> omega
  · intro helper member
    have bound:=Listing8HeadTemplateFields.xor_bounds mode (head mode l) helper member
    right
    have lower : Listing8DirectionLayout.endPC mode (head mode l)≤address := placed.1
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at heads <;> omega
  · intro template member
    cases mode
    all_goals simp only [StatePointerField,reduceCtorEq,true_and,false_and,or_false] at chosen
    all_goals rcases chosen with rfl | rfl
    all_goals simp only [Listing8StateTemplateFields.arithmetic,Listing8StateLayout.packets,Listing8StateLayout.newPackets,
      Listing8StateLayout.masks,Listing8StateLayout.updates,Listing8DirectionLayout.group,List.map_append,List.map_cons,List.map_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [DwordPacketTemplateRuns.template,DwordTemplateCollection.Compatible,DwordTemplateCollection.start,
      DwordTemplateCollection.span,DwordTemplateCollection.field,DwordTemplateCollection.width,
      Listing8StateLayout.newPC,Listing8StateLayout.maskPC,Listing8StateLayout.updatePC,Listing8StateLayout.halves,
      Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize]
  · intro entry member
    exact Or.inr ((Listing8StateTemplateFields.fixed_bounds mode _ entry member).2.trans placed.2.1)


theorem copied_field (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (pc : Nat) (member : pc∈Listing8OwnerImage.pointerPositions mode l) (address count : Nat)
    (within : pointerField mode pc≤address ∧ address+count≤pointerField mode pc+mode.wordBytes) :
    Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) address count := by
  have range:=Listing8OwnerImage.pointer_bounds mode l pc member
  have before:=ctx.resources.inputAfter
  have fieldEnd : pointerField mode pc+mode.wordBytes≤pc+pointerSpan mode := by
    cases mode <;> simp [pointerField,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize,Mode.wordBytes]
  exact exterior mode l _ _ address count (Or.inl (within.2.trans (fieldEnd.trans (range.2.trans before))))

theorem copied_halves (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (pc : Nat) (member : pc∈Listing8OwnerImage.pointerPositions mode l) (start target : Nat) :
    ∀ layout∈Listing8PointerCopies.split mode start (pointerField mode pc) target,
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) layout.source 4 := by
  intro layout inside
  cases mode
  all_goals simp only [Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at inside
  all_goals rcases inside with rfl | rfl
  all_goals apply copied_field _ origin l t g node rule ctx pc member
  all_goals simp [Mode.wordBytes,Nat.add_assoc]

theorem word_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
      (Listing8PointerCopies.word mode l).source mode.wordBytes ∧
    Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
      (Listing8PointerCopies.word mode l).destination mode.wordBytes := by
  constructor
  · exact copied_field mode origin l t g node rule ctx (transitionParams mode l).destination
      (by simp [Listing8OwnerImage.pointerPositions]) _ _ ⟨Nat.le_refl _,Nat.le_refl _⟩
  · exact exterior mode l _ _ _ _ (Or.inl ((Listing8PointerCopies.cursor_before mode l).trans ctx.resources.inputAfter))

theorem dword_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ layout∈Listing8PointerCopies.layouts mode l t,
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) layout.source 4 ∧
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) layout.destination 4 := by
  intro layout member
  simp only [Listing8PointerCopies.layouts,List.mem_append] at member
  rcases member with (state | back) | forward
  · refine ⟨copied_halves mode origin l t g node rule ctx _ (by simp [Listing8OwnerImage.pointerPositions]) _ _ layout state,?_⟩
    cases mode
    all_goals simp only [Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at state
    all_goals rcases state with rfl | rfl
    all_goals apply state_pointer_field
    all_goals rw [ctx.body.state.state]
    all_goals simp [StatePointerField,Nat.add_assoc]
  · refine ⟨copied_halves mode origin l t g node rule ctx _ (by simp [Listing8OwnerImage.pointerPositions]) _ _ layout back,?_⟩
    cases mode
    all_goals simp only [Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at back
    all_goals rcases back with rfl | rfl
    all_goals apply head_pointer_field
    all_goals rw [ctx.body.state.head.back]
    all_goals simp [HeadPointerField,Nat.add_assoc]
  · refine ⟨copied_halves mode origin l t g node rule ctx _ (by simp [Listing8OwnerImage.pointerPositions]) _ _ layout forward,?_⟩
    cases mode
    all_goals simp only [Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at forward
    all_goals rcases forward with rfl | rfl
    all_goals apply head_pointer_field
    all_goals rw [ctx.body.state.head.forward]
    all_goals simp [HeadPointerField,Nat.add_assoc]


end SmcTuring.Appendix.Listing8JointLocalPrefixFields

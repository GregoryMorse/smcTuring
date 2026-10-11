module
public import SmcTuring.Appendix.Listing8JointDeclarationCatalog
public import SmcTuring.Appendix.Listing8GlobalResetBindings
public import SmcTuring.Appendix.Listing8ResetStoreRegions
public import SmcTuring.Appendix.Listing8JointObserverGeometry
public import SmcTuring.Appendix.Listing8GlobalMaintainedTerminalTemplates

public section
namespace SmcTuring.Appendix.Listing8JointResetCatalog
open Native Listing8CopyImage Listing8SourceGraph Listing8JointDeclarationCatalog
abbrev Targets:=Listing8PointerCopies.Targets
abbrev region (mode : Mode) (origin : Nat) (l : Layout) (g : Graph):=Listing8LoopHaltImage.region mode origin l g
set_option maxHeartbeats 2000000

/-- Full-word cursor writes, the exact failure initializer word and CALL
operand, and late reset stores preserve every inactive local descriptor. -/
theorem local_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Listing8ResetStoreRegions.Allowed mode (region mode origin l g) address count) :
    Listing8JointLocalCatalog.Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) address count := by
  have cursor := Listing8InputBounds.cursor_bounds mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources
  have transition := Listing8PointerCopies.cursor_before mode l
  have call := Listing8JointLocalPrefixFields.call_before_table mode origin l t g node rule ctx
  have before := ctx.resources.inputAfter
  have callEq := Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode (Listing8JointLocalCatalog.failure mode l (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.callPC mode origin at callEq
  have resetStart : Listing8FullTableImage.start mode origin≤(region mode origin l g).start := by
    simp only [region,Listing8LoopHaltImage.region,Listing8TableResetImage.region,Listing8TransitionTable.endPC];omega
  have owner : (region mode origin l g).start≤StringInit.field mode (Listing8ResetLayout.ownerPC mode (region mode origin l g)) := by
    simp only [StringInit.field,Listing8ResetLayout.ownerPC,Listing8ResetLayout.inputCopy,ConversionLayout.endPC,
      ConversionLayout.thirdPC,ConversionLayout.secondPC];omega
  have marker : (region mode origin l g).start≤Listing8ResetLayout.markerPC mode (region mode origin l g)+6 := by
    simp only [Listing8ResetLayout.markerPC,Listing8ResetLayout.transitionCopy,Listing8ResetLayout.ownerPC,
      Listing8ResetLayout.inputCopy,ConversionLayout.endPC,ConversionLayout.thirdPC,ConversionLayout.secondPC];omega
  simp only [Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
  rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · apply Listing8JointLocalContinuation.failure_fields mode origin l t g node rule ctx
    simp only [Listing8FailureStoreRegions.Allowed,Listing8FailureStoreRegions.fields,region,Listing8LoopHaltImage.region,Listing8TableResetImage.region]
    rw [callEq]
    simp
  · apply Listing8JointLocalContinuation.failure_fields mode origin l t g node rule ctx
    simp [Listing8FailureStoreRegions.Allowed,Listing8FailureStoreRegions.fields,region,Listing8LoopHaltImage.region,Listing8TableResetImage.region,Listing8JointLocalCatalog.failure,Listing8BootControl.region]
  · exact Listing8JointLocalPrefixFields.exterior mode l _ _ _ _ (Or.inl cursor.2.2.1)
  · exact Listing8JointLocalPrefixFields.exterior mode l _ _ _ _ (Or.inr (call.trans (resetStart.trans owner)))
  · exact Listing8JointLocalPrefixFields.exterior mode l _ _ _ _ (Or.inr call)
  · exact Listing8JointLocalPrefixFields.exterior mode l _ _ _ _ (Or.inl (transition.trans before))
  · exact Listing8JointLocalPrefixFields.exterior mode l _ _ _ _ (Or.inr (call.trans (resetStart.trans marker)))


theorem field_classes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Listing8ResetStoreRegions.Allowed mode (region mode origin l g) address count) :
    (address=StringCodec.sourceField mode l.start ∧ count=mode.wordBytes) ∨
    (address=StringCodec.sourceField mode (secondStart mode l) ∧ count=mode.wordBytes) ∨ codeEnd mode l≤address := by
  have tableBefore := Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have order := Listing8JointLocalCatalog.ordering mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have codeBefore := ctx.resources.inputAfter
  have jumpBefore := (Listing8GlobalMainBounds.copy mode origin l t g node rule ctx).2
  have globalOrder := Listing8GlobalControlLayout.ordered mode origin
  have resetStart : Listing8FullTableImage.start mode origin≤(region mode origin l g).start := by
    simp only [region,Listing8LoopHaltImage.region,Listing8TableResetImage.region,Listing8TransitionTable.endPC];omega
  have owner : (region mode origin l g).start≤StringInit.field mode (Listing8ResetLayout.ownerPC mode (region mode origin l g)) := by
    simp only [StringInit.field,Listing8ResetLayout.ownerPC,Listing8ResetLayout.inputCopy,ConversionLayout.endPC,
      ConversionLayout.thirdPC,ConversionLayout.secondPC];omega
  have marker : (region mode origin l g).start≤Listing8ResetLayout.markerPC mode (region mode origin l g)+6 := by
    simp only [Listing8ResetLayout.markerPC,Listing8ResetLayout.transitionCopy,Listing8ResetLayout.ownerPC,
      Listing8ResetLayout.inputCopy,ConversionLayout.endPC,ConversionLayout.thirdPC,ConversionLayout.secondPC];omega
  have source : codeEnd mode l≤Listing8FailureLayout.source mode (Listing8BootControl.region mode origin l (nodePC mode origin g g.halt)) := by
    change codeEnd mode l≤(Listing8JointLocalCatalog.failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start+10+StringCodec.fieldOffset mode
    omega
  simp only [Listing8ResetStoreRegions.Allowed,Listing8ResetStoreRegions.fields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at allowed
  rcases allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · right;right
    change codeEnd mode l≤Listing8JumpLayout.callPC mode origin+1
    omega
  · exact Or.inr (Or.inr source)
  · exact Or.inl ⟨ctx.body.state.head.input.fields.cursorLabel,rfl⟩
  · exact Or.inr (Or.inr (tableBefore.trans (resetStart.trans owner)))
  · exact Or.inr (Or.inr tableBefore)
  · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
  · exact Or.inr (Or.inr (tableBefore.trans (resetStart.trans marker)))

theorem retarget_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (allowed : Listing8ResetStoreRegions.Allowed mode (region mode origin l g) address count) :
    DwordTemplateCollection.CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) address count := by
  have first := Listing8InputCrossCatalogFields.cursor_before_second mode l
  have second := StringMacroLayout.field_coordinates mode (transitionParams mode l)
  have endFirst := endpoint_lower mode (secondStart mode l) (Listing8Prototypes.transitionSpan mode)
  change secondStart mode l≤patchStart mode l at endFirst
  have earlySecond : StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes≤patchStart mode l := by
    change secondStart mode l≤StringCodec.sourceField mode (secondStart mode l) ∧
      StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes≤StringCodec.destinationField mode (secondStart mode l) ∧ _ at second
    have middle := second.2.2.1
    change StringCodec.destinationField mode (secondStart mode l)+mode.wordBytes≤StringMacroLayout.bodyStart mode (transitionParams mode l) at middle
    have upper : StringMacroLayout.destinationTail mode (transitionParams mode l)≤patchStart mode l := second.2.2.2.2.2
    omega
  intro template member
  have bounds := Listing8RetargetExecutableTemplates.bounds mode (patchLayout mode l) template member
  have lower : patchStart mode l≤DwordTemplateCollection.start template := bounds.1
  have upper : DwordTemplateCollection.start template+DwordTemplateCollection.span template≤codeEnd mode l := bounds.2
  right
  rcases field_classes mode origin l t g node rule ctx address count allowed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | late
  · exact Or.inl ((first.trans endFirst).trans lower)
  · exact Or.inl (earlySecond.trans lower)
  · exact Or.inr (upper.trans late)

theorem macro_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (current : Listing8MacroPointerFrames.Property mode l memory)
    (allowed : Listing8ResetStoreRegions.Allowed mode (region mode origin l g) address bytes.length) :
    Listing8MacroPointerFrames.Property mode l (ByteMemory.putBytes memory address bytes) := by
  rcases field_classes mode origin l t g node rule ctx address bytes.length allowed with ⟨rfl,size⟩ | ⟨rfl,size⟩ | late
  · exact ⟨StringMacroTemplates.operand_store mode (nodeParams mode l) memory _ bytes current.1
      (Or.inl ⟨le_refl _,by rw [size];exact le_refl _⟩),
      StringMacroTemplates.frame mode (transitionParams mode l) memory _ bytes current.2
        (Or.inl (by rw [size];exact Listing8InputCrossCatalogFields.cursor_before_second mode l))⟩
  · have lower : secondStart mode l≤StringCodec.sourceField mode (secondStart mode l) := by unfold StringCodec.sourceField;omega
    exact ⟨StringMacroTemplates.frame mode (nodeParams mode l) memory _ bytes current.1 (Or.inr lower),
      StringMacroTemplates.operand_store mode (transitionParams mode l) memory _ bytes current.2
        (Or.inl ⟨le_refl _,by rw [size];exact le_refl _⟩)⟩
  · have dest := destinations mode l
    have before : patchStart mode l≤codeEnd mode l := by
      have node : patchStart mode l+40≤codeEnd mode l := by
        change (nodeParams mode l).destination≤codeEnd mode l
        omega
      omega
    exact Listing8MacroPointerFrames.store mode l memory address bytes current (Or.inl (before.trans late))

theorem store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (current : Inactive mode origin l g memory)
    (allowed : Listing8ResetStoreRegions.Allowed mode (region mode origin l g) address bytes.length) :
    Inactive mode origin l g (ByteMemory.putBytes memory address bytes) :=
  ⟨Listing8JointLocalCatalog.store mode l _ _ memory address bytes current.1 (local_fields mode origin l t g node rule ctx _ _ allowed),
    DwordTemplateCollection.store_all _ memory address bytes current.2.1 (retarget_fields mode origin l t g node rule ctx _ _ allowed),
    macro_fields mode origin l t g node rule ctx memory address bytes current.2.2 allowed⟩

theorem states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode)
    (current : Inactive mode origin l g state.principal.memory)
    (bounds : Listing8ResetLayout.Bounds mode (region mode origin l g))
    (entry : state.principal.pc=Arithmetic.encodeNat mode (region mode origin l g).start)
    (image : Listing8ResetPackets.Initial mode (region mode origin l g) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Inactive mode origin l g reached.principal.memory)
      ((Listing8ResetLayout.program mode (region mode origin l g)).map (StringStoreWrites.liftDword mode)) state :=
  StringStoreTemplateRuns.preserve mode _ _ _ state current
    (fun memory address bytes kept fields => store mode origin l t g node rule ctx memory address bytes kept fields)
    (Listing8ResetStoreRegions.regions mode (region mode origin l g) bounds state entry image)


theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringTemplateStates.Run mode (fun reached =>
      Inactive mode origin l g reached.principal.memory ∧
      Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory ∧
      (∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),DwordTemplateCollection.Decodes mode template reached.principal.memory) ∧
      StringEncodedTemplates.Decodes mode (nodeParams mode l) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (transitionParams mode l) reached.principal.memory ∧
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8ResetExecutableTemplates.Decodes mode (region mode origin l g) reached.principal.memory)
      ((Listing8ResetLayout.program mode (region mode origin l g)).map (StringStoreWrites.liftDword mode))
      (Listing8LoopTable.finish mode origin l t g node rule state) := by
  have declarations := Listing8JointDeclarationCatalog.transitions mode origin l t g node rule ctx old state image.control halted
  have table := StringDwordWritesBridge.trace mode (Listing8LoopTable.table_trace mode origin l t g node rule ctx old state image.control halted)
  have seed := StringTemplateStates.at_prefix mode _ _ [] (Listing8LoopControl.finish mode origin l t g node rule state)
    (by simpa only [List.append_nil] using declarations)
  rw [StringWrites.trace_run_eq mode table] at seed
  have inactive := states mode origin l t g node rule ctx _ seed.2.1
    (Listing8GraphInputContext.reset_bounds mode origin l t g node rule ctx).reset
    (Listing8LoopTable.endpoint mode origin l t g node rule ctx old state image.control halted)
    (Listing8LoopHaltImage.after_table mode origin l t g node rule ctx old state image halted)
  have own := Listing8GlobalResetBindings.maintained mode origin l t g node rule ctx old state image halted
  exact StringTemplateStates.monotone mode _ _ _ _ (fun reached pair =>
    ⟨pair.1,Listing8JointLocalCatalog.decodes mode l _ _ reached.principal.memory pair.1.1,
      (fun template member => DwordTemplateCollection.decodes mode template reached.principal.memory (pair.1.2.1 template member)),
      StringEncodedTemplates.macro_decodes mode (nodeParams mode l) reached.principal.memory
        (by change Listing8Prototypes.nodeSpan mode<2^31;cases mode <;> decide) pair.1.2.2.1,
      StringEncodedTemplates.macro_decodes mode (transitionParams mode l) reached.principal.memory
        (by change Listing8Prototypes.transitionSpan mode<2^31;cases mode <;> decide) pair.1.2.2.2,
      pair.2.1,pair.2.2⟩)
    (JointTemplateStates.join mode _ _ _ _ inactive own)

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    Inactive mode origin l g (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory := by
  have all := maintained mode origin l t g node rule ctx old state image halted
  have endState := StringTemplateStates.at_prefix mode _ _ [] (Listing8LoopTable.finish mode origin l t g node rule state)
    (by simpa only [List.append_nil] using all)
  have actual := StringDwordWritesBridge.trace mode (Listing8LoopReset.reset_trace mode origin l t g node rule ctx old state image halted)
  rw [StringWrites.trace_run_eq mode actual] at endState
  exact endState.1


theorem observer_store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (current : Listing8OwnerTemplateCollection.All mode (Owners mode origin l (values mode origin g node rule) g) memory)
    (placed : address+bytes.length≤patchStart mode l ∨
      (codeEnd mode l≤address ∧ address+bytes.length≤Listing8FullTableImage.start mode origin) ∨
      (Listing8TransitionTable.endPC mode (Listing8FullTableImage.start mode origin) (table mode origin g)≤address ∧
        address+bytes.length≤Listing8GraphLayout.input mode origin g.transitions)) :
    Listing8OwnerTemplateCollection.All mode (Owners mode origin l (values mode origin g node rule) g)
      (ByteMemory.putBytes memory address bytes) :=
  Listing8CopyOwnerLifetimes.store mode _ memory current ⟨address,bytes⟩
    (Listing8JointObserverGeometry.outside mode origin l t g node rule ctx ⟨address,bytes⟩ placed)

theorem cursor_ends (mode : Mode) (l : Layout)
    (fields : Listing8InputBounds.Fields mode l) :
    l.input.cursor+mode.wordBytes≤patchStart mode l ∧ (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤patchStart mode l := by
  have first := Listing8InputCrossCatalogFields.cursor_before_second mode l
  have lower := endpoint_lower mode (secondStart mode l) (Listing8Prototypes.transitionSpan mode)
  change secondStart mode l≤patchStart mode l at lower
  have second := StringMacroLayout.field_coordinates mode (transitionParams mode l)
  have middle := second.2.2.1
  change StringCodec.destinationField mode (secondStart mode l)+mode.wordBytes≤StringMacroLayout.bodyStart mode (transitionParams mode l) at middle
  have source := second.2.1
  change StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes≤StringCodec.destinationField mode (secondStart mode l) at source
  have upper : StringMacroLayout.destinationTail mode (transitionParams mode l)≤patchStart mode l := second.2.2.2.2.2
  constructor
  · rw [fields.cursorLabel];exact first.trans lower
  · change StringCodec.sourceField mode (secondStart mode l)+mode.wordBytes≤patchStart mode l
    omega

theorem observers_endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    Listing8OwnerTemplateCollection.All mode (Owners mode origin l (values mode origin g node rule) g)
      (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory := by
  have seed : Listing8OwnerTemplateCollection.All mode (Owners mode origin l (values mode origin g node rule) g)
      (Listing8LoopTable.finish mode origin l t g node rule state).principal.memory := by
    rw [(Listing8LoopTable.result mode origin l t g node rule ctx old state image.control halted).2.1]
    exact (Listing8JointDeclarationCatalog.endpoint_seed mode origin l t g node rule ctx old state image.control).2
  have cursors := cursor_ends mode l ctx.body.state.head.input.fields
  have jumps := Listing8GlobalControlLayout.ordered mode origin
  have before := (Listing8GlobalMainBounds.copy mode origin l t g node rule ctx).2
  rw [Listing8LoopReset.effect mode origin l t g node rule ctx old state image halted]
  unfold ByteMemory.putWord DwordCode.put
  apply observer_store mode origin l t g node rule ctx
  · apply observer_store mode origin l t g node rule ctx
    · apply observer_store mode origin l t g node rule ctx _ _ _ seed
      right;left
      rw [LittleEndian.word_encode_length]
      constructor <;> omega
    · left;rw [LittleEndian.word_encode_length]
      exact cursors.1
  · left;rw [LittleEndian.word_encode_length]
    exact cursors.2

/-- Every updated trailing node declaration keeps all inactive executable
families and the complete source/copied observer set at its SAME prefix.
Its single word snapshot comes from the actual original declaration trace. -/
theorem nodes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringTemplateStates.Run mode
      (fun reached => Listing8JointDeclarationCatalog.Property mode origin l (values mode origin g node rule) g
        (Listing8NodeTable.owners mode (Listing8GraphLayout.input mode origin g.transitions)
          (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule)))
        (Listing8LoopReset.finish mode origin l t g node rule state).principal.memory reached.principal.memory)
      ((Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions)
        (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))).map (StringStoreWrites.liftDword mode))
      (Listing8LoopReset.finish mode origin l t g node rule state) := by
  have bounds := Listing8GraphStep.native_bounds mode origin g node rule ctx.native
  have current := (Listing8LoopResetOutput.source_graph mode origin l t g node rule ctx old state image halted).1
  have entry := Listing8LoopTerminal.input_entry mode origin l t g node rule ctx old state image halted
  have placed := Listing8GlobalDeclarationRegions.nodes mode origin (Listing8GraphStep.updated g node rule) bounds
  have writes := Listing8DeclarationWrites.nodes_owned mode _ _ _ _
    (Listing8GraphNodeImage.valid mode origin (Listing8GraphStep.updated g node rule) bounds) placed _ entry current
  have regions := BoundedStoreRegions.interval mode (fun address _ => Listing8FullTableImage.start mode origin≤address)
    _ _ _ _ (fun _ _ lower _ => lower) writes
  have inactive := inactive_states mode origin l t g node rule ctx _ _ (endpoint mode origin l t g node rule ctx old state image halted) regions
  have actual := Listing8GlobalDeclarationBindings.nodes mode origin (Listing8GraphStep.updated g node rule) bounds _ entry current
    (Listing8GlobalMaintainedTerminalTemplates.reset_property mode origin l t g node rule ctx old state image halted)
  have allOwners := observers_endpoint mode origin l t g node rule ctx old state image halted
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun reached pair => joined mode origin l _ g _ _ reached.principal.memory pair.1.1 pair.2 allOwners pair.1.2)
    (JointTemplateStates.join mode _ _ _ _ actual inactive)

end SmcTuring.Appendix.Listing8JointResetCatalog

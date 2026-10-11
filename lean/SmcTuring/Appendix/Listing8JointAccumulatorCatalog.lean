module
public import SmcTuring.Appendix.Listing8OriginalControlImage
public import SmcTuring.Appendix.Listing8JointResetObserverRun
public import SmcTuring.Appendix.Listing8AccumulatorRestored
public import SmcTuring.Native.AccumulatorStoreRegions

public section
namespace SmcTuring.Appendix.Listing8JointAccumulatorCatalog
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8OwnerTemplateCollection
open Listing8JointDeclarationCatalog
abbrev Targets:=Listing8PointerCopies.Targets
abbrev graphEnd (mode : Mode) (origin : Nat) (g : Graph):=Listing8GraphLayout.endPC mode origin g.transitions g.nodes
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8GlobalControlTemplates.Property mode origin memory ∧ Inactive mode origin l g memory ∧
  All mode (Owners mode origin l v g) memory

theorem original_upper (mode : Mode) (origin : Nat) (g : Graph) (template : Template mode)
    (member : template∈Listing8OriginalGraphCatalog.catalog mode origin g) :
    start mode template+span mode template≤graphEnd mode origin g := by
  simp only [Listing8OriginalGraphCatalog.catalog,List.mem_append,List.mem_flatten] at member
  rcases member with ⟨items,selected,inside⟩ | ⟨items,selected,inside⟩
  · obtain ⟨query,rfl⟩ := List.mem_ofFn.mp selected
    exact (Listing8OriginalGraphCatalog.node_bounds mode _ template inside).2.trans
      (Listing8GraphLayout.node_upper mode origin g.transitions g.nodes query.val query.isLt)
  · obtain ⟨query,rfl⟩ := List.mem_ofFn.mp selected
    exact (Listing8OriginalGraphCatalog.rule_bounds mode _ template inside).2.trans
      ((Listing8GraphLayout.transition_upper mode origin g.transitions query.val query.isLt).trans
        ((Listing8GraphLayout.table_before_input mode origin g.transitions).trans
          (Listing8GraphLayout.node_lower mode origin g.transitions g.nodes)))

theorem table_before_end (mode : Mode) (origin : Nat) (g : Graph) :
    Listing8FullTableImage.start mode origin≤graphEnd mode origin g :=
  (Listing8GraphLayout.transition_lower mode origin g.transitions).trans
    ((Listing8GraphLayout.table_before_input mode origin g.transitions).trans
      (Listing8GraphLayout.node_lower mode origin g.transitions g.nodes))

theorem owner_upper (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (template : Template mode) (member : template∈Owners mode origin l (values mode origin g node rule) g) :
    start mode template+span mode template≤graphEnd mode origin g := by
  rcases List.mem_append.mp member with copied | original
  · rcases Listing8JointObserverGeometry.copied_classification mode origin l t g node rule ctx template copied with physical | original
    · exact physical.2.trans ((Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed).trans (table_before_end mode origin g))
    · exact original_upper mode origin g template original
  · exact original_upper mode origin g template original

/-- One generic late-word/store frame for the full original and copied
observer inventory. Accumulator slots lie beyond the entire graph. -/
theorem observer_store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (current : All mode (Owners mode origin l (values mode origin g node rule) g) memory)
    (late : graphEnd mode origin g≤address) :
    All mode (Owners mode origin l (values mode origin g node rule) g) (ByteMemory.putBytes memory address bytes) := by
  intro template member
  exact frame mode template memory (current template member) ⟨address,bytes⟩
    (Or.inr ((owner_upper mode origin l t g node rule ctx template member).trans late))

theorem store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (current : Property mode origin l (values mode origin g node rule) g memory)
    (late : graphEnd mode origin g≤address) :
    Property mode origin l (values mode origin g node rule) g (ByteMemory.putBytes memory address bytes) := by
  have tableBefore := (table_before_end mode origin g).trans late
  exact ⟨Listing8GlobalControlTemplates.store mode origin memory address bytes current.1 (Or.inr (Or.inr (Or.inr tableBefore))),
    Listing8JointDeclarationCatalog.store mode origin l t g node rule ctx memory address bytes current.2.1 tableBefore,
    observer_store mode origin l t g node rule ctx memory address bytes current.2.2 late⟩

/-- Every reached boundary decodes all inactive families and all exact
source/copied observers; the common observer active packet is empty. -/
theorem decodes (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) (memory : ByteMemory.Memory)
    (current : Property mode origin l v g memory) :
    Listing8GlobalControlTemplates.Decodes mode origin memory ∧
    Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) memory ∧
    (∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),DwordTemplateCollection.Decodes mode template memory) ∧
    StringEncodedTemplates.Decodes mode (nodeParams mode l) memory ∧
    StringEncodedTemplates.Decodes mode (transitionParams mode l) memory ∧
    Listing8JointResetObserverRun.Certificate mode origin l v g memory :=
  ⟨Listing8GlobalControlTemplates.decodes mode origin memory current.1,
    Listing8JointLocalCatalog.decodes mode l _ _ memory current.2.1.1,
    (fun template member => DwordTemplateCollection.decodes mode template memory (current.2.1.2.1 template member)),
    StringEncodedTemplates.macro_decodes mode (nodeParams mode l) memory
      (by change Listing8Prototypes.nodeSpan mode<2^31;cases mode <;> decide) current.2.1.2.2.1,
    StringEncodedTemplates.macro_decodes mode (transitionParams mode l) memory
      (by change Listing8Prototypes.transitionSpan mode<2^31;cases mode <;> decide) current.2.1.2.2.2,
    Listing8JointResetObserverRun.empty mode origin l v g memory current.2.2⟩

theorem epilogue (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode a.epilogue)
    (current : Property mode origin l (values mode origin g node rule) g state.principal.memory)
    (saveAfter : graphEnd mode origin g≤a.save) (pointerAfter : graphEnd mode origin g≤a.pointer) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (Listing8AccumulatorExit.program mode a) state :=
  StringStoreTemplateRuns.preserve mode _ _ _ state current
    (store mode origin l t g node rule ctx)
    (AccumulatorStoreRegions.epilogue mode (fun address _ => graphEnd mode origin g≤address) a valid state entry saveAfter pointerAfter)

/-- This seed is derived from the actual terminal declaration/reset traces.
It is not a hypothesis about an epilogue state. -/
theorem terminal_seed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    Property mode origin l (values mode origin g node rule) g (Listing8LoopTerminal.finish mode origin l t g node rule state).principal.memory := by
  have all := Listing8JointResetCatalog.nodes mode origin l t g node rule ctx old state image halted
  have endpoint := StringTemplateStates.at_prefix mode _ _ [] (Listing8LoopReset.finish mode origin l t g node rule state)
    (by simpa only [List.append_nil] using all)
  have actual := StringDwordWritesBridge.trace mode (Listing8LoopTerminal.input_trace mode origin l t g node rule ctx old state image halted)
  rw [StringWrites.trace_run_eq mode actual] at endpoint
  refine ⟨Listing8GlobalMaintainedTerminalTemplates.property mode origin l t g node rule ctx old state image halted,endpoint.2.1,?_⟩
  rw [(Listing8LoopTerminal.result mode origin l t g node rule ctx old state image halted).2.1]
  exact Listing8JointResetCatalog.observers_endpoint mode origin l t g node rule ctx old state image halted

/-- The actual terminal endpoint supplies the full catalog for all three
accumulator epilogue instructions at SAME native prefixes. -/
theorem maintained_epilogue (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : a.epilogue=graphEnd mode origin g)
    (saveAfter : graphEnd mode origin g≤a.save) (pointerAfter : graphEnd mode origin g≤a.pointer) :
    StringTemplateStates.Run mode (fun reached => Property mode origin l (values mode origin g node rule) g reached.principal.memory)
      (Listing8AccumulatorExit.program mode a) (Listing8LoopTerminal.finish mode origin l t g node rule state) :=
  epilogue mode origin l t g node rule ctx a valid _
    (by rw [located];exact (Listing8LoopTerminal.result mode origin l t g node rule ctx old state image halted).1)
    (terminal_seed mode origin l t g node rule ctx old state image halted) saveAfter pointerAfter


@[expose] def BeforeProperty (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8GlobalControlTemplates.Property mode origin memory ∧
  Listing8OriginalControlImage.PreCatalog mode origin l g memory ∧
  All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory

theorem before_store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (current : BeforeProperty mode origin l g memory) (late : graphEnd mode origin g≤address) :
    BeforeProperty mode origin l g (ByteMemory.putBytes memory address bytes) := by
  have tableBefore := (table_before_end mode origin g).trans late
  have before := Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have call := Listing8JointLocalPrefixFields.call_before_table mode origin l t g node rule ctx
  have dest := destinations mode l
  have patchBefore : patchStart mode l+40≤codeEnd mode l := by
    change (nodeParams mode l).destination≤codeEnd mode l
    omega
  refine ⟨Listing8GlobalControlTemplates.store mode origin memory address bytes current.1 (Or.inr (Or.inr (Or.inr tableBefore))),
    ⟨Listing8JointLocalCatalog.store mode l _ _ memory address bytes current.2.1.1
      (Listing8JointLocalPrefixFields.exterior mode l _ _ address bytes.length (Or.inr (call.trans tableBefore))),
      Listing8MacroPointerFrames.store mode l memory address bytes current.2.1.2.1 (Or.inl (by omega)),
      DwordTemplateCollection.store_all _ memory address bytes current.2.1.2.2 ?_⟩,?_⟩
  · intro template member
    have upper := (Listing8CopyOwnerLifetimeRun.patch_bounds mode l template member).2
    exact Or.inr (Or.inr (by omega))
  · intro template member
    exact frame mode template memory (current.2.2 template member) ⟨address,bytes⟩
      (Or.inr ((original_upper mode origin g template member).trans late))

/-- The actual accumulator entry store preserves the complete pre-copy
catalog and original graph; no copied header is asserted before creation. -/
theorem prologue (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (saveAfter : graphEnd mode origin g≤a.save)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => BeforeProperty mode origin l g reached.principal.memory)
      [StringStack.native mode (AccumulatorLayout.saveForm mode a)]
      (Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed) := by
  have initial : BeforeProperty mode origin l g
      (Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed).principal.memory :=
    ⟨Listing8GlobalControlTemplates.initial mode origin _ (Listing8GlobalInitialControl.current mode origin l t g node rule ctx memory seed),
      Listing8OriginalControlImage.pre_catalog mode origin l t g node rule ctx memory seed,
      Listing8OriginalGraphBootstrap.initial mode origin l t g node rule ctx memory seed⟩
  exact StringStoreTemplateRuns.preserve mode _ _ _ _ initial (before_store mode origin l t g node rule ctx)
    (AccumulatorStoreRegions.prologue mode (fun address _ => graphEnd mode origin g≤address) a valid _ rfl saveAfter)

/-- The bootstrap catalog is observed after the actual accumulator save,
whose memory is commuted with original emission by the established theorem. -/
theorem saved_bootstrap (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : AccumulatorLayout.savedPC mode a=origin)
    (saveAfter : graphEnd mode origin g≤a.save)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (nodeParams mode l) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (transitionParams mode l) reached.principal.memory ∧
      (∀ template∈Listing8CopyOwnerLifetimeRun.patches mode l,DwordTemplateCollection.Decodes mode template reached.principal.memory) ∧
      All mode (Listing8OriginalGraphCatalog.catalog mode origin g) reached.principal.memory)
      (Listing4EntryLayout.forms mode origin)
      (Listing8AccumulatorEntry.saved mode origin l t g node rule a memory seed) := by
  rw [Listing8AccumulatorEntry.saved_eq mode origin l t g node rule ctx a valid located saveAfter memory seed]
  exact Listing8OriginalControlImage.bootstrap mode origin l t g node rule ctx _ seed

/-- The accepted full main invariant is bound at SAME prefixes of the actual
accumulator save + bootstrap + first main run,without a state reset bridge. -/
theorem saved_bootstrap_main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : AccumulatorLayout.savedPC mode a=origin) (saveAfter : graphEnd mode origin g≤a.save)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (present : ByteMemory.bytesAt (Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed).principal.memory a.prologue
      (Native.encode mode (AccumulatorLayout.saveForm mode a)).length=Native.encode mode (AccumulatorLayout.saveForm mode a))
    (before after : List (StringStack.Form mode))
    (cut : Listing8LoopControl.program mode origin l t g node rule
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule (ByteMemory.putWord mode memory a.save seed.principal.accumulator) seed)=before++after) :
    Listing8JointCopyOwnerLifetimes.PrefixInvariant mode origin l t g node rule
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule (ByteMemory.putWord mode memory a.save seed.principal.accumulator) seed) before
      (StringWrites.run mode ([StringStack.native mode (AccumulatorLayout.saveForm mode a)]++Listing4EntryLayout.forms mode origin++before)
        (Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed)) := by
  rw [StringWrites.run_append,StringWrites.run_append,
    StringWrites.trace_run_eq mode (Listing8AccumulatorEntry.trace mode origin l t g node rule a valid memory seed present),
    Listing8AccumulatorEntry.saved_eq mode origin l t g node rule ctx a valid located saveAfter memory seed,
    Listing8GraphEntryWrites.boot_run mode origin l t g node rule ctx _ seed]
  exact Listing8OriginalControlImage.main mode origin l t g node rule ctx _ seed before after cut


@[expose] def declarationOwners (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  Listing8TransitionTable.owners mode (Listing8FullTableImage.start mode origin) (table mode origin g)++
    Listing8NodeTable.owners mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
@[expose] def TerminalCertificate (mode : Mode) (origin : Nat) (l : Layout) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) :=
  ∃ packet : StringWrites.Packet,
    (Listing8OriginalOwnerRegions.Allowed mode (declarationOwners mode origin g node rule) packet ∨
      (packet.bytes=[] ∨ (packet.address=StringInit.field mode (Listing8ResetLayout.ownerPC mode (Listing8LoopHaltImage.region mode origin l g)) ∨
        packet.address=(Listing8LoopHaltImage.region mode origin l g).ttape) ∧ packet.bytes.length=mode.wordBytes)) ∧
    ∀ template∈Owners mode origin l (values mode origin g node rule) g,Outside mode template packet →
      Intact mode template memory ∧ Decodes mode template memory
@[expose] def TerminalProperty (mode : Mode) (origin : Nat) (l : Layout) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) :=
  Listing8GlobalControlTemplates.Decodes mode origin memory ∧ Inactive mode origin l g memory ∧
  Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) memory ∧
  (∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),DwordTemplateCollection.Decodes mode template memory) ∧
  StringEncodedTemplates.Decodes mode (nodeParams mode l) memory ∧
  StringEncodedTemplates.Decodes mode (transitionParams mode l) memory ∧
  TerminalCertificate mode origin l g node rule memory
@[expose] def tailForms (mode : Mode) (origin : Nat) (l : Layout) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout) :=
  ((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map (StringStoreWrites.liftDword mode))++
  ((Listing8ResetLayout.program mode (Listing8LoopHaltImage.region mode origin l g)).map (StringStoreWrites.liftDword mode))++
  ((Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions)
    (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))).map (StringStoreWrites.liftDword mode))++
  Listing8AccumulatorExit.program mode a

theorem declaration_certificate (mode : Mode) (origin : Nat) (l : Layout) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (owners : List (Listing8OriginalOwners.Owner mode))
    (initial memory : ByteMemory.Memory) (members : ∀ owner∈owners,owner∈declarationOwners mode origin g node rule)
    (current : Certificate mode owners (Owners mode origin l (values mode origin g node rule) g) initial memory) :
    TerminalCertificate mode origin l g node rule memory := by
  obtain ⟨packet,allowed,_,headers⟩ := current
  refine ⟨packet,Or.inl ?_,headers⟩
  rcases allowed with restored | ⟨pc,value,member,active,size⟩
  · exact Or.inl restored
  · exact Or.inr ⟨pc,value,members _ member,active,size⟩

/-- All terminal declaration/reset/accumulator phases share one precise
architectural word certificate. Each earlier phase theorem retains its
stronger phase-specific address and positive restoration statement. -/
theorem terminal_tail (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : a.epilogue=graphEnd mode origin g)
    (saveAfter : graphEnd mode origin g≤a.save) (pointerAfter : graphEnd mode origin g≤a.pointer) :
    StringTemplateStates.Run mode (fun reached => TerminalProperty mode origin l g node rule reached.principal.memory)
      (tailForms mode origin l g node rule a) (Listing8LoopControl.finish mode origin l t g node rule state) := by
  have transitions := StringTemplateStates.monotone mode _ _ _ _ (fun reached kept =>
    (show TerminalProperty mode origin l g node rule reached.principal.memory from ⟨kept.1,kept.2.1,kept.2.2.1,kept.2.2.2.1,kept.2.2.2.2.1,kept.2.2.2.2.2.1,
      declaration_certificate mode origin l g node rule _ _ reached.principal.memory
        (fun owner member => List.mem_append_left _ member) kept.2.2.2.2.2.2⟩))
    (Listing8JointDeclarationCatalog.transitions mode origin l t g node rule ctx old state image.control halted)
  have reset := StringTemplateStates.monotone mode _ _ _ _ (fun reached kept =>
    (show TerminalProperty mode origin l g node rule reached.principal.memory from ⟨kept.2.2.2.2.2.1,kept.1,kept.2.1,kept.2.2.1,kept.2.2.2.1,kept.2.2.2.2.1,
      (by obtain ⟨packet,allowed,headers⟩ := kept.2.2.2.2.2.2.2;exact ⟨packet,Or.inr allowed,headers⟩)⟩))
    (Listing8JointResetObserverRun.maintained mode origin l t g node rule ctx old state image halted)
  have nodes := StringTemplateStates.monotone mode _ _ _ _ (fun reached kept =>
    (show TerminalProperty mode origin l g node rule reached.principal.memory from ⟨kept.1,kept.2.1,kept.2.2.1,kept.2.2.2.1,kept.2.2.2.2.1,kept.2.2.2.2.2.1,
      declaration_certificate mode origin l g node rule _ _ reached.principal.memory
        (fun owner member => List.mem_append_right _ member) kept.2.2.2.2.2.2⟩))
    (Listing8JointResetCatalog.nodes mode origin l t g node rule ctx old state image halted)
  have last := StringTemplateStates.monotone mode _ _ _ _ (fun reached kept =>
    (show TerminalProperty mode origin l g node rule reached.principal.memory from by
      have decoded := decodes mode origin l _ g reached.principal.memory kept
      refine ⟨decoded.1,kept.2.1,decoded.2.1,decoded.2.2.1,decoded.2.2.2.1,decoded.2.2.2.2.1,?_⟩
      obtain ⟨packet,allowed,headers⟩ := decoded.2.2.2.2.2
      exact ⟨packet,Or.inr allowed,headers⟩))
    (maintained_epilogue mode origin l t g node rule ctx old state image halted a valid located saveAfter pointerAfter)
  have tableRun := StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (Listing8LoopTable.table_trace mode origin l t g node rule ctx old state image.control halted))
  have resetRun := StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (Listing8LoopReset.reset_trace mode origin l t g node rule ctx old state image halted))
  have nodeRun := StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (Listing8LoopTerminal.input_trace mode origin l t g node rule ctx old state image halted))
  rw [tailForms,StringTemplateStates.append,StringTemplateStates.append,StringTemplateStates.append]
  simp only [StringWrites.run_append,tableRun,resetRun,nodeRun]
  exact ⟨⟨⟨transitions,reset⟩,nodes⟩,last⟩

end SmcTuring.Appendix.Listing8JointAccumulatorCatalog

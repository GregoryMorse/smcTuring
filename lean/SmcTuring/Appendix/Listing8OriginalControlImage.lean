module
public import SmcTuring.Appendix.Listing8OriginalGraphMainEntry
public import SmcTuring.Appendix.Listing8GlobalInitialControl
public import SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes

public section
namespace SmcTuring.Appendix.Listing8OriginalControlImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev old:=Listing8OriginalGraphMainEntry.old
abbrev afterBoot:=Listing8GraphCopyWrites.afterBoot

/-- The actual bootstrap restores the full originally emitted memory. -/
theorem memory (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (afterBoot mode origin l t g node rule backing seed).principal.memory=
      (Listing8GraphBackedge.initial mode origin l t g node rule backing seed).principal.memory := by
  have effect := Listing4Entry.effect mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule backing seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body)
  change (Listing4Entry.finish mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule backing seed)).principal.memory=_
  rw [effect]
  rfl

theorem direction (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopDirectionImage.Current mode (Listing8DirectionGeometry.region mode l)
      (afterBoot mode origin l t g node rule backing seed).principal.memory := by
  rw [afterBoot,Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx backing seed]
  exact ⟨Listing8DirectionImage.initial_helpers mode l t _ ctx.resources ctx.body.state.head _,
    Listing8DirectionImage.initial_headers mode l t _ ctx.resources ctx.body.state.head _,
    Listing8HeadImage.initial_xor mode l t _ ctx.resources ctx.body.state.head _,
    Listing8HeadImage.initial_headers mode l t _ ctx.resources ctx.body.state.head _⟩

theorem state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopStateImage.Current mode (Listing8StateGeometry.region mode l)
      (afterBoot mode origin l t g node rule backing seed).principal.memory := by
  rw [afterBoot,Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx backing seed]
  exact ⟨Listing8StateImage.initial_helpers mode l t _ ctx.resources ctx.body.state _,
    Listing8StateImage.initial_headers mode l t _ ctx.resources ctx.body.state _⟩

theorem failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8FailureReuseImage.Current mode
      (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
      (afterBoot mode origin l t g node rule backing seed).principal.memory := by
  rw [afterBoot,Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx backing seed]
  exact Listing8FailureReuseImage.from_initial mode _ _
    (Listing8FailureGlobalImage.initial_region mode l t _ _ _ ctx.resources ctx.body _)

/-- All original graph,local and global images are derived at the SAME actual
first main state. No image of a future native state is a premise. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8LoopControlImage.Current mode origin l t g node rule old
      (afterBoot mode origin l t g node rule backing seed) := by
  refine ⟨⟨⟨⟨Listing8OriginalGraphMainEntry.current mode origin l t g node rule ctx backing seed,
    direction mode origin l t g node rule ctx backing seed⟩,state mode origin l t g node rule ctx backing seed⟩,
    failure mode origin l t g node rule ctx backing seed⟩,?_,?_,?_,?_⟩
  all_goals rw [memory mode origin l t g node rule ctx backing seed]
  · exact Listing8GlobalInitialControl.entry mode origin l t g node rule backing seed
  · exact Listing8GlobalInitialControl.prefix_image mode origin l t g node rule ctx backing seed
  · exact Listing8GlobalInitialControl.call_image mode origin l t g node rule ctx backing seed
  · exact Listing8GlobalInitialControl.fail_image mode origin l t g node rule ctx backing seed

/-- The accepted joint maintained invariant applies to EVERY prefix of the
first main iteration,at the actual bootstrap endpoint. -/
theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (before after : List (StringStack.Form mode))
    (cut : Listing8LoopControl.program mode origin l t g node rule
      (afterBoot mode origin l t g node rule backing seed)=before++after) :
    Listing8JointCopyOwnerLifetimes.PrefixInvariant mode origin l t g node rule
      (afterBoot mode origin l t g node rule backing seed) before
      (StringWrites.run mode before (afterBoot mode origin l t g node rule backing seed)) :=
  Listing8JointCopyOwnerLifetimes.complete mode origin l t g node rule ctx old _
    (current mode origin l t g node rule ctx backing seed) before after cut


@[expose] def PreCatalog (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (bytes : ByteMemory.Memory) :=
  Listing8JointLocalCatalog.Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) bytes ∧
  Listing8MacroPointerFrames.Property mode l bytes ∧
  DwordTemplateCollection.All (Listing8CopyOwnerLifetimeRun.patches mode l) bytes

theorem pre_catalog (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    PreCatalog mode origin l g (Listing8GraphBackedge.initial mode origin l t g node rule backing seed).principal.memory := by
  rw [←memory mode origin l t g node rule ctx backing seed]
  have present := current mode origin l t g node rule ctx backing seed
  have graph := present.body.state.head.graph
  exact ⟨Listing8JointLocalPrefixRun.initial mode origin l t g node rule ctx old _ present,
    ⟨StringMacroTemplates.initial mode _ _ (Listing8MainCopyImage.macro_current mode _ _ graph.nodeMacro),
      StringMacroTemplates.initial mode _ _ (Listing8MainCopyImage.macro_current mode _ _ graph.ruleMacro)⟩,
    Listing8CopyOwnerLifetimeRun.patches_initial mode l _ _
      (Listing8GlobalOriginalPrefix.copying mode origin l t g node rule ctx backing seed)⟩

/-- A single early-store frame covers all bootstrap writes for all pre-copy
executable families; it does not assert a copied header before its birth. -/
theorem early_store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (bytes : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (kept : PreCatalog mode origin l g bytes) (early : address+packet.length≤l.start) :
    PreCatalog mode origin l g (ByteMemory.putBytes bytes address packet) := by
  have input := (coordinates mode l).2.2
  have first := endpoint_lower mode l.start (Listing8Prototypes.nodeSpan mode)
  change l.start≤secondStart mode l at first
  have second := endpoint_lower mode (secondStart mode l) (Listing8Prototypes.transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  have order := Listing8JointLocalCatalog.ordering mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have outside : address+packet.length≤l.input.start := by
    have start : l.start≤l.input.start := ctx.resources.inputAfter.trans' (by
      have dest := destinations mode l
      omega)
    exact early.trans start
  refine ⟨Listing8JointLocalCatalog.store mode l _ _ bytes address packet kept.1
    (Listing8JointLocalCatalog.exterior mode l _ _ _ _ (Or.inl outside) (Or.inl (by omega))),
    ⟨StringMacroTemplates.frame mode _ bytes address packet kept.2.1.1 (Or.inl early),
      StringMacroTemplates.frame mode _ bytes address packet kept.2.1.2 (Or.inl (early.trans first))⟩,
    DwordTemplateCollection.store_all _ bytes address packet kept.2.2 ?_⟩
  intro template member
  have bound := Listing8CopyOwnerLifetimeRun.patch_bounds mode l template member
  exact Or.inr (Or.inl (early.trans (first.trans (second.trans bound.1))))

/-- Every actual bootstrap prefix keeps the same local/macro/pre-copy patch
catalogs and full original graph, jointly with the proved global decoder. -/
theorem bootstrap (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (nodeParams mode l) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (transitionParams mode l) reached.principal.memory ∧
      (∀ template∈Listing8CopyOwnerLifetimeRun.patches mode l,DwordTemplateCollection.Decodes mode template reached.principal.memory) ∧
      Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) reached.principal.memory)
      (Listing4EntryLayout.forms mode origin) (Listing8GraphBackedge.initial mode origin l t g node rule backing seed) := by
  have stores := BoundedStoreRegions.monotone mode (Listing4StackTemplates.Slots mode origin)
    (fun address count => address+count≤l.start) _ _
    (Listing8ControlStoreFields.slot_bound mode origin l t g node rule ctx)
    (Listing4EntrySlotRegions.entry mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule backing seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))
  have all := StringStoreTemplateRuns.preserve mode _ _ _ _ (pre_catalog mode origin l t g node rule ctx backing seed)
    (early_store mode origin l t g node rule ctx) stores
  have globalGraph := Listing8OriginalGraphBootstrap.all_states mode origin l t g node rule ctx backing seed
  exact StringTemplateStates.monotone mode _ _ _ _ (fun reached pair =>
    ⟨pair.1.1,Listing8JointLocalCatalog.decodes mode l _ _ reached.principal.memory pair.2.1,
      StringEncodedTemplates.macro_decodes mode (nodeParams mode l) reached.principal.memory
        (by change Listing8Prototypes.nodeSpan mode<2^31;cases mode <;> decide) pair.2.2.1.1,
      StringEncodedTemplates.macro_decodes mode (transitionParams mode l) reached.principal.memory
        (by change Listing8Prototypes.transitionSpan mode<2^31;cases mode <;> decide) pair.2.2.1.2,
      (fun template member => DwordTemplateCollection.decodes mode template reached.principal.memory (pair.2.2.2 template member)),pair.1.2⟩)
    (JointTemplateStates.join mode _ _ _ _ globalGraph all)


/-- The first main invariant is observed after the actual bootstrap prefix
in the same original execution,using its deterministic proved endpoint. -/
theorem bootstrap_then_main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (before after : List (StringStack.Form mode))
    (cut : Listing8LoopControl.program mode origin l t g node rule
      (afterBoot mode origin l t g node rule backing seed)=before++after) :
    Listing8JointCopyOwnerLifetimes.PrefixInvariant mode origin l t g node rule
      (afterBoot mode origin l t g node rule backing seed) before
      (StringWrites.run mode ((Listing4EntryLayout.forms mode origin)++before)
        (Listing8GraphBackedge.initial mode origin l t g node rule backing seed)) := by
  rw [StringWrites.run_append,Listing8GraphEntryWrites.boot_run mode origin l t g node rule ctx backing seed]
  exact main mode origin l t g node rule ctx backing seed before after cut

end SmcTuring.Appendix.Listing8OriginalControlImage

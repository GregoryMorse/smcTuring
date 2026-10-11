module
public import SmcTuring.Appendix.Listing8JointCopyOwnerLifetimes
public import SmcTuring.Appendix.Listing8GlobalDeclarationBindings
public import SmcTuring.Appendix.Listing8LoopControlFrames

public section
namespace SmcTuring.Appendix.Listing8JointDeclarationCatalog
open Native Listing8CopyImage Listing8SourceGraph Listing8OwnerTemplateCollection
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

@[expose] def Inactive (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8JointLocalCatalog.Property mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) memory ∧
  DwordTemplateCollection.All (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) memory ∧
  Listing8MacroPointerFrames.Property mode l memory
@[expose] def Owners (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph) :=
  Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l v)++Listing8OriginalGraphCatalog.catalog mode origin g
@[expose] def Certificate (mode : Mode) (owners : List (Listing8OriginalOwners.Owner mode))
    (templates : List (Template mode)) (initial memory : ByteMemory.Memory) :=
  ∃ packet : StringWrites.Packet,Listing8OriginalOwnerRegions.Allowed mode owners packet ∧
    memory=ByteMemory.putBytes initial packet.address packet.bytes ∧
    ∀ template∈templates,Outside mode template packet → Intact mode template memory ∧ Decodes mode template memory
@[expose] def Property (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph)
    (owners : List (Listing8OriginalOwners.Owner mode)) (initial memory : ByteMemory.Memory) :=
  Listing8GlobalControlTemplates.Decodes mode origin memory ∧ Inactive mode origin l g memory ∧
  Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) memory ∧
  (∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),DwordTemplateCollection.Decodes mode template memory) ∧
  StringEncodedTemplates.Decodes mode (nodeParams mode l) memory ∧
  StringEncodedTemplates.Decodes mode (transitionParams mode l) memory ∧
  Certificate mode owners (Owners mode origin l v g) initial memory

theorem snapshot (mode : Mode) (owners : List (Listing8OriginalOwners.Owner mode)) (templates : List (Template mode))
    (initial memory : ByteMemory.Memory) (intact : All mode templates initial)
    (current : Listing8OriginalOwnerRegions.Certificate mode owners initial memory) :
    Certificate mode owners templates initial memory := by
  obtain ⟨packet,allowed,actual,_⟩ := current
  refine ⟨packet,allowed,actual,?_⟩
  intro template member outside
  rw [actual]
  have kept := Listing8OwnerTemplateCollection.frame mode template initial (intact template member) packet outside
  exact ⟨kept,decodes mode template _ kept⟩

theorem store (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (current : Inactive mode origin l g memory) (late : Listing8FullTableImage.start mode origin≤address) :
    Inactive mode origin l g (ByteMemory.putBytes memory address bytes) := by
  have before := Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have call := Listing8JointLocalPrefixFields.call_before_table mode origin l t g node rule ctx
  have patch : patchStart mode l≤address := by
    have d := destinations mode l
    have ordered : patchStart mode l+40≤codeEnd mode l := by
      change (nodeParams mode l).destination≤codeEnd mode l
      omega
    omega
  refine ⟨Listing8JointLocalCatalog.store mode l _ _ memory address bytes current.1
    (Listing8JointLocalPrefixFields.exterior mode l _ _ address bytes.length (Or.inr (call.trans late))),?_,
    Listing8MacroPointerFrames.store mode l memory address bytes current.2.2 (Or.inl patch)⟩
  intro template member
  have bound := Listing8RetargetExecutableTemplates.bounds mode (patchLayout mode l) template member
  apply DwordTemplateCollection.store template memory address bytes (current.2.1 template member)
  right;right
  have endCode := Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have upper : DwordTemplateCollection.start template+DwordTemplateCollection.span template≤codeEnd mode l := bound.2
  exact upper.trans (endCode.trans late)

theorem inactive_states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (current : Inactive mode origin l g state.principal.memory)
    (regions : StringStoreRegions.Run mode (fun address _ => Listing8FullTableImage.start mode origin≤address) forms state) :
    StringTemplateStates.Run mode (fun reached => Inactive mode origin l g reached.principal.memory) forms state :=
  StringStoreTemplateRuns.preserve mode _ _ forms state current
    (fun memory address bytes kept late => store mode origin l t g node rule ctx memory address bytes kept late) regions

theorem joined (mode : Mode) (origin : Nat) (l : Layout) (v : Values mode) (g : Graph)
    (owners : List (Listing8OriginalOwners.Owner mode)) (initial memory : ByteMemory.Memory)
    (global : Listing8GlobalControlTemplates.Decodes mode origin memory)
    (inactive : Inactive mode origin l g memory) (intact : All mode (Owners mode origin l v g) initial)
    (current : Listing8OriginalOwnerRegions.Certificate mode owners initial memory) :
    Property mode origin l v g owners initial memory :=
  ⟨global,inactive,Listing8JointLocalCatalog.decodes mode l _ _ memory inactive.1,
    (fun template member => DwordTemplateCollection.decodes mode template memory (inactive.2.1 template member)),
    StringEncodedTemplates.macro_decodes mode (nodeParams mode l) memory (by change Listing8Prototypes.nodeSpan mode<2^31;cases mode <;> decide) inactive.2.2.1,
    StringEncodedTemplates.macro_decodes mode (transitionParams mode l) memory (by change Listing8Prototypes.transitionSpan mode<2^31;cases mode <;> decide) inactive.2.2.2,
    snapshot mode owners _ initial memory intact current⟩

theorem catalog_updated (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    Listing8OriginalGraphCatalog.catalog mode origin (Listing8GraphStep.updated g node rule)=
      Listing8OriginalGraphCatalog.catalog mode origin g := rfl

theorem endpoint_seed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    Inactive mode origin l g (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory ∧
    All mode (Owners mode origin l (values mode origin g node rule) g)
      (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory := by
  have localCatalog := Listing8JointLocalMain.endpoint mode origin l t g node rule ctx old state current
  have fixed := Listing8JointControlCatalog.endpoint mode origin l t g node rule ctx old state current
  have graph := Listing8LoopControlFrames.source_graph mode origin l t g node rule ctx old state current
  have originals := Listing8OriginalGraphCatalog.from_initial mode origin (Listing8GraphStep.updated g node rule) _ graph.1
    (Listing8MainGraphTable.updated_table_current mode origin g node rule _ graph.2)
  rw [catalog_updated] at originals
  refine ⟨⟨localCatalog.2.1,fixed.1,fixed.2.1⟩,?_⟩
  intro template member
  rcases List.mem_append.mp member with copied | original
  · exact fixed.2.2 template copied
  · exact originals template original

theorem transitions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8LoopControlImage.Current mode origin l t g node rule old state)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringTemplateStates.Run mode
      (fun reached => Property mode origin l (values mode origin g node rule) g
        (Listing8TransitionTable.owners mode (Listing8FullTableImage.start mode origin) (table mode origin g))
        (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory reached.principal.memory)
      ((Listing8TableTrace.program mode (Listing8FullTableImage.start mode origin) (table mode origin g)).map (StringStoreWrites.liftDword mode))
      (Listing8LoopControl.finish mode origin l t g node rule state) := by
  have seed := endpoint_seed mode origin l t g node rule ctx old state current
  have placed := Listing8GlobalDeclarationRegions.transitions mode origin g ctx.native
  have writes := Listing8DeclarationWrites.transitions_owned mode _ _ _ _
    (Listing8GraphTableBounds.declarations_valid mode origin g ctx.native) placed _
    (Listing8LoopTable.table_entry mode origin l t g node rule ctx old state current halted)
    (Listing8LoopControlFrames.source_graph mode origin l t g node rule ctx old state current).2
  have regions := BoundedStoreRegions.interval mode (fun address _ => Listing8FullTableImage.start mode origin≤address)
    _ _ _ _ (fun _ _ lower _ => lower) writes
  have inactive := inactive_states mode origin l t g node rule ctx _ _ seed.1 regions
  have actual := Listing8GlobalDeclarationBindings.maintained mode origin l t g node rule ctx old state current halted
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun reached pair => joined mode origin l _ g _ _ reached.principal.memory pair.1.1 pair.2 seed.2 pair.1.2)
    (JointTemplateStates.join mode _ _ _ _ actual inactive)

end SmcTuring.Appendix.Listing8JointDeclarationCatalog

module
public import SmcTuring.Appendix.Listing8GlobalOriginalPrefix
public import SmcTuring.Appendix.Listing8GlobalInputRegions
public import SmcTuring.Appendix.Listing8GlobalSelectionRegions
public import SmcTuring.Appendix.Listing8GraphFailureWrites

public section
namespace SmcTuring.Appendix.Listing8GlobalOriginalBodyRegions
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
attribute [local irreducible] StringStoreRegions.Run
abbrev Targets:=Listing8PointerCopies.Targets

theorem input_phase (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      (((Listing8LiteralComposition.program mode l.input (values mode origin g node rule).rule
        (values mode origin g node rule).tape (values mode origin g node rule).fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphPointerWrites.finish mode origin l t g node rule memory seed) := by
  rw [Listing8GraphInputWrites.pointer_state mode origin l t g node rule ctx memory seed]
  apply StringStoreRegions.mixed
  exact Listing8InputTemplateRegions.mask_complete mode l.input _ _ force _ force ctx.resources.inputFits
    (Listing8InputBounds.masks mode l ctx.body.state.head.input.fields)
    (Listing8InputBounds.update mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources)
    (Listing8InputBounds.outside mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources) _
    (Listing8GlobalInput.entry mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input _ _)
    (Listing8GlobalInput.input_image mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input _ _)
    (Listing8GlobalInput.cursor mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input _ _)
    _ (Listing8GlobalInputRegions.fields mode origin l t g node rule ctx)

theorem input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      (Listing8GraphInputWrites.forms mode l t (values mode origin g node rule))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  rw [Listing8GraphInputWrites.forms,Listing8GlobalInput.program,List.map_append,StringStoreRegions.append]
  change StringStoreRegions.Run mode _ (Listing8GraphPointerWrites.forms mode l t (values mode origin g node rule)) _ ∧
    StringStoreRegions.Run mode _ _ (StringWrites.run mode
      (Listing8GraphPointerWrites.forms mode l t (values mode origin g node rule))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed))
  rw [Listing8GraphInputWrites.pointer_run mode origin l t g node rule ctx memory seed]
  exact ⟨Listing8GlobalOriginalPrefix.forms_regions mode origin l t g node rule ctx memory seed,
    input_phase mode origin l t g node rule ctx memory seed⟩

theorem direction (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      (Listing8GraphDirectionWrites.forms mode origin l t g node rule memory seed)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  rw [Listing8GraphDirectionWrites.forms,StringStoreRegions.append,
    Listing8GraphDirectionWrites.input_run mode origin l t g node rule ctx memory seed]
  exact ⟨input mode origin l t g node rule ctx memory seed,
    Listing8GlobalSelectionRegions.direction mode origin l t g node rule ctx _
      (Listing8GraphInputWrites.endpoint mode origin l t g node rule ctx memory seed)⟩

theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      (Listing8GraphHeadWrites.forms mode origin l t g node rule memory seed)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  rw [Listing8GraphHeadWrites.forms,StringStoreRegions.append,
    Listing8GraphHeadWrites.direction_run mode origin l t g node rule ctx memory seed]
  exact ⟨direction mode origin l t g node rule ctx memory seed,
    Listing8GlobalSelectionRegions.head mode origin l t g node rule ctx _
      (Listing8GraphDirectionWrites.endpoint mode origin l t g node rule ctx memory seed)⟩

theorem state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      (Listing8GraphStateWrites.forms mode origin l t g node rule memory seed)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  rw [Listing8GraphStateWrites.forms,StringStoreRegions.append,
    Listing8GraphStateWrites.head_run mode origin l t g node rule ctx memory seed]
  exact ⟨head mode origin l t g node rule ctx memory seed,
    Listing8GlobalSelectionRegions.state mode origin l t g node rule ctx _
      (Listing8GraphHeadWrites.endpoint mode origin l t g node rule ctx memory seed)⟩

/-- Every complete store in the original first main body, from the actual
bootstrap result through failure selection, preserves the global headers. -/
theorem failure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      (Listing8GraphFailureWrites.forms mode origin l t g node rule memory seed)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have current:=Listing8FailureGlobalImage.current_region mode l t (values mode origin g node rule)
    (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  change Listing8FailureImage.Initial mode (Listing8GraphFailureWrites.region mode origin l g)
    (Listing8GlobalFailure.entryState mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory at current
  rw [←Listing8GraphFailureWrites.state_state mode origin l t g node rule ctx memory seed] at current
  rw [Listing8GraphFailureWrites.forms,StringStoreRegions.append,
    Listing8GraphFailureWrites.state_run mode origin l t g node rule ctx memory seed]
  exact ⟨state mode origin l t g node rule ctx memory seed,
    Listing8GlobalFailureRegions.regions mode origin _ (Listing8GlobalFailureRegions.graph_geometry mode origin l t g node rule ctx)
      (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
      (Listing8GraphStateWrites.endpoint mode origin l t g node rule ctx memory seed)
      (Listing8FailureReuseImage.from_initial mode _ _ current)⟩

end SmcTuring.Appendix.Listing8GlobalOriginalBodyRegions

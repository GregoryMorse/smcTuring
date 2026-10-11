module
public import SmcTuring.Appendix.Listing8JointOriginalGraphCopies

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphRetarget
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringTemplateStates.Run

theorem copies_endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g)
      (Listing8MainCopies.finish mode l state).principal.memory := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  have initial:=Listing8OriginalGraphCatalog.from_initial mode origin g _ current.nodes current.rules
  have bounds:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  have nodeEnd : (nodeParams mode l).destination+nodeSpan mode≤codeEnd mode l := by
    have exactEnd : (nodeParams mode l).destination+nodeSpan mode+transitionSpan mode=codeEnd mode l := rfl
    omega
  have ruleEnd : (transitionParams mode l).destination+transitionSpan mode=codeEnd mode l := rfl
  rw [Listing8MainCopies.effect mode l _ ctx.resources state current.entry current.forward image.prefixCurrent.copying]
  apply Listing8OriginalGraphFailureRun.store mode origin g
  · exact Listing8OriginalGraphFailureRun.store mode origin g _ _ _ initial (by
      rw [sourceNodeBytes,node_length];omega)
  · rw [sourceTransitionBytes,transition_length];omega

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Listing8LiveRetarget.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (fun address count => address+count≤Listing8FullTableImage.start mode origin)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have input:=Listing8GlobalMainBounds.input mode origin l t g node rule ctx
  have bounds:=Listing8InitializerWrites.tape_bounds mode (Listing4EntryLayout.mainPC mode origin)
    (Listing8JumpLayout.jumpPC mode origin) l ctx.resources input
  have patches:=StringRetargetWrites.owned mode (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin)
    _ (patchStart mode l) (Listing8ModeOffsets.chain mode (patchLayout mode l))
    (Listing8ModeOffsets.valid mode _ (block_capacity mode l ctx.resources) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)))
    (Listing8GlobalRetargetRegions.patch_fields mode origin l t g node rule ctx) state entry
  have trace:=StringDwordWritesBridge.trace mode (Listing8LiveRetarget.patch_trace mode l _ ctx.resources state entry current)
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  rw [Listing8LiveRetarget.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  constructor
  · exact BoundedStoreRegions.interval mode _ _ _ _ state (fun _ _ _ upper => by omega) patches
  · exact BoundedStoreRegions.interval mode _ _ _ [StringStoreWrites.liftDword mode (Listing8Initializer.tapeForm mode l (values mode origin g node rule))]
      _ (fun _ _ _ upper => by omega)
      ⟨StringStoreWrites.located mode _ _ (nodeParams mode l).destination (Listing8LiteralInput.sourceField mode l.input)
        (values mode origin g node rule).tape _ (Listing8LiveRetarget.patched_pc mode l ctx.resources state entry)
        ctx.fields.tapeReach bounds.1 bounds.2,trivial⟩

theorem all_states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (current : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached => Listing8OwnerTemplateCollection.All mode
      (Listing8OriginalGraphCatalog.catalog mode origin g) reached.principal.memory)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) (Listing8MainCopies.finish mode l state) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  exact StringStoreTemplateRuns.preserve mode _ _ _ _ (copies_endpoint mode origin l t g node rule ctx old state current)
    (Listing8OriginalGraphFailureRun.store mode origin g)
    (regions mode origin l t g node rule ctx _ (Listing8MainCopies.registers mode l _ ctx.resources state current.entry current.forward image.prefixCurrent.copying).1
      (Listing8MainCopies.retarget_current mode l _ ctx.resources state current.entry current.forward image.prefixCurrent.copying))

end SmcTuring.Appendix.Listing8OriginalGraphRetarget

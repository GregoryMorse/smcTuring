module
public import SmcTuring.Appendix.Listing8GlobalCopyRegions
public import SmcTuring.Appendix.Listing8MainRetargetWrites

public section
namespace SmcTuring.Appendix.Listing8GlobalRetargetRegions
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem patch_fields (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ site∈Listing8ModeOffsets.sites mode (patchLayout mode l),
      Listing4EntryLayout.mainPC mode origin≤site.owner+2 ∧ site.owner+6≤Listing8JumpLayout.jumpPC mode origin := by
  have block:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have before:=endpoint_lower mode l.start (Listing8Prototypes.nodeSpan mode)
  change l.start≤secondStart mode l at before
  have next:=endpoint_lower mode (secondStart mode l) (Listing8Prototypes.transitionSpan mode)
  change secondStart mode l≤patchStart mode l at next
  intro site member
  have bounds:=Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member
  change patchStart mode l+40≤site.owner ∧ site.owner+10≤codeEnd mode l ∧ _ at bounds
  constructor <;> omega

theorem retarget (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Listing8LiveRetarget.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have input:=Listing8GlobalMainBounds.input mode origin l t g node rule ctx
  have bounds:=Listing8InitializerWrites.tape_bounds mode (Listing4EntryLayout.mainPC mode origin)
    (Listing8JumpLayout.jumpPC mode origin) l ctx.resources input
  have patches:=StringRetargetWrites.owned mode (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin)
    _ (patchStart mode l) (Listing8ModeOffsets.chain mode (patchLayout mode l))
    (Listing8ModeOffsets.valid mode _ (block_capacity mode l ctx.resources) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)))
    (patch_fields mode origin l t g node rule ctx) state entry
  have trace:=StringDwordWritesBridge.trace mode (Listing8LiveRetarget.patch_trace mode l _ ctx.resources state entry current)
  rw [Listing8LiveRetarget.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  constructor
  · exact BoundedStoreRegions.interval mode _ _ _ _ state (fun _ _ lower upper => Or.inr (Or.inl ⟨lower,upper⟩)) patches
  · exact BoundedStoreRegions.interval mode _ _ _ _ _ (fun _ _ lower upper => Or.inr (Or.inl ⟨lower,upper⟩))
      ⟨StringStoreWrites.located mode _ _ (nodeParams mode l).destination (Listing8LiteralInput.sourceField mode l.input)
        (values mode origin g node rule).tape _ (Listing8LiveRetarget.patched_pc mode l ctx.resources state entry)
        ctx.fields.tapeReach bounds.1 bounds.2,trivial⟩

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8MainRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have mapping : (((Listing8MainCopies.program mode l).map StringDword.Form.string).map (StringStoreWrites.liftDword mode))=
      (Listing8MainCopies.program mode l).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
  have firstRun : StringWrites.run mode ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state=
      Listing8MainCopies.finish mode l state := by
    apply StringWrites.trace_run_eq mode
    have lifting : (fun form : StringForm.Form mode => StringStack.Form.previous (StringControl.Form.previous (StringDword.Form.string form)))=
        StringWrites.liftString mode := by funext form;rfl
    simpa only [List.map_map,Function.comp_def,lifting] using StringStack.previous_trace mode (StringControl.previous_trace mode
      (StringDword.string_trace mode (Listing8MainCopies.trace mode l _ ctx.resources state entry forward current)))
  rw [Listing8MainRetarget.program,List.map_append,mapping,StringStoreRegions.append,firstRun]
  exact ⟨Listing8GlobalCopyRegions.regions mode origin l t g node rule ctx state entry forward current,
    retarget mode origin l t g node rule ctx _ (Listing8MainCopies.registers mode l _ ctx.resources state entry forward current).1
      (Listing8MainCopies.retarget_current mode l _ ctx.resources state entry forward current)⟩

end SmcTuring.Appendix.Listing8GlobalRetargetRegions

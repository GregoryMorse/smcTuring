module
public import SmcTuring.Appendix.Listing8GlobalMainBounds
public import SmcTuring.Appendix.Listing8GlobalMacroRegions
public import SmcTuring.Appendix.Listing8MainCopyWrites

public section
namespace SmcTuring.Appendix.Listing8GlobalCopyRegions
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem placements (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    Listing8GlobalMacroRegions.Placement mode origin (nodeParams mode l) ∧
      Listing8GlobalMacroRegions.Placement mode origin (transitionParams mode l) := by
  have block:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have originals:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have coords:=coordinates mode l
  have destinations:=Listing8CopyImage.destinations mode l
  have word:=Listing8CopyWriteBounds.spans mode
  have first:=endpoint_lower mode l.start (nodeSpan mode)
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change l.start≤secondStart mode l at first
  change secondStart mode l≤patchStart mode l at second
  constructor
  · refine ⟨?_,Or.inr (Or.inr (Or.inr originals.1)),?_⟩
    · change Listing4EntryLayout.mainPC mode origin≤l.start ∧ secondStart mode l≤Listing8JumpLayout.jumpPC mode origin
      exact ⟨block.1,by omega⟩
    · right;left
      change Listing4EntryLayout.mainPC mode origin≤(nodeParams mode l).destination ∧
        (nodeParams mode l).destination+max (nodeSpan mode) mode.wordBytes≤Listing8JumpLayout.jumpPC mode origin
      rw [Nat.max_eq_left word.1]
      constructor <;> omega
  · refine ⟨?_,Or.inr (Or.inr (Or.inr originals.2)),?_⟩
    · change Listing4EntryLayout.mainPC mode origin≤secondStart mode l ∧ patchStart mode l≤Listing8JumpLayout.jumpPC mode origin
      constructor <;> omega
    · right;left
      change Listing4EntryLayout.mainPC mode origin≤(transitionParams mode l).destination ∧
        (transitionParams mode l).destination+max (transitionSpan mode) mode.wordBytes≤Listing8JumpLayout.jumpPC mode origin
      rw [Nat.max_eq_left word.2]
      constructor <;> omega

/-- Both actual MOVS macros derive their readiness from the same present
main image and the preceding complete copy. Source and destination buffers
are kept separate in the global preservation policy. -/
theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have placed:=placements mode origin l t g node rule ctx
  have ready:=Listing8LiveCopies.first_ready mode l ctx.resources state entry forward
    (Listing8MainCopyImage.node_current mode l _ _ current)
  have next:=Listing8LiveCopies.second_ready mode l ctx.resources state ready
    (Listing8MainCopyImage.rule_current mode l _ _ current)
  change StringStoreRegions.Run mode _
    (((StringProgram.forms mode l.start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size)++
      (StringProgram.forms mode (secondStart mode l) (transitionParams mode l).source
        (transitionParams mode l).destination (transitionParams mode l).size)).map (StringWrites.liftString mode)) state
  rw [List.map_append,StringStoreRegions.append]
  constructor
  · exact Listing8GlobalMacroRegions.regions mode origin _ placed.1 state ready
  · have firstRun : StringWrites.run mode
        ((StringProgram.forms mode l.start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size).map
          (StringWrites.liftString mode)) state=Listing8CopyTrace.first mode l state := by
      apply StringWrites.trace_run_eq mode
      have lifting : (fun form : StringForm.Form mode => StringStack.Form.previous (StringControl.Form.previous (StringDword.Form.string form)))=
          StringWrites.liftString mode := by funext form;rfl
      simpa only [List.map_map,Function.comp_def,Listing8CopyTrace.first,lifting,nodeParams] using
        StringStack.previous_trace mode (StringControl.previous_trace mode
          (StringDword.string_trace mode (StringMacroTrace.trace mode _ _ ready)))
    rw [firstRun]
    exact Listing8GlobalMacroRegions.regions mode origin _ placed.2 _ next

end SmcTuring.Appendix.Listing8GlobalCopyRegions

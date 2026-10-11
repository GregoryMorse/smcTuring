module
public import SmcTuring.Appendix.Listing8GlobalMainOwnerRegions
public import SmcTuring.Appendix.Listing8GlobalPointerRegions
public import SmcTuring.Appendix.Listing8MainPrefixWrites

public section
namespace SmcTuring.Appendix.Listing8GlobalMainPrefixRegions
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

/-- The complete actual main copy/retarget/owner/pointer prefix derives all
global store regions from the present image and source-graph values. -/
theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainPrefix.Current mode l t (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have trace:=StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.trace mode l _ ctx.resources
    (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward current.copying)
  rw [Listing8MainPrefix.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  exact ⟨Listing8GlobalMainOwnerRegions.regions mode origin l t g node rule ctx state entry forward current.copying,
    Listing8GlobalPointerRegions.regions mode origin l t g node rule ctx _
      (Listing8MainLiveOwners.registers mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx)
        ctx.fields.tapeReach state entry forward current.copying).1⟩

end SmcTuring.Appendix.Listing8GlobalMainPrefixRegions

module
public import SmcTuring.Appendix.Listing8GlobalMainBounds
public import SmcTuring.Appendix.Listing8LoopStateWrites
public import SmcTuring.Native.BoundedStoreRegions

public section
namespace SmcTuring.Appendix.Listing8GlobalSelectionRegions
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem direction (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8DirectionGeometry.region mode l).start) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l) state).map (StringStoreWrites.liftDword mode)) state :=
  BoundedStoreRegions.interval mode _ _ _ _ state (fun _ _ lower upper => Or.inr (Or.inl ⟨lower,upper⟩))
    (Listing8DirectionWrites.owned mode (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin) _
      (Listing8GlobalMainBounds.direction mode origin l t g node rule ctx) ctx.body.state.head.capacity state entry)

theorem head (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8DirectionLayout.selectionEnd mode (Listing8DirectionGeometry.region mode l))) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l) state).map (StringStoreWrites.liftDword mode)) state :=
  BoundedStoreRegions.interval mode _ _ _ _ state (fun _ _ lower upper => Or.inr (Or.inl ⟨lower,upper⟩))
    (Listing8HeadTailWrites.owned mode (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin) _
      (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head)
      (Listing8GlobalMainBounds.direction mode origin l t g node rule ctx)
      (Listing8GlobalMainBounds.cursor mode origin l t g node rule ctx) state entry)

theorem state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (machine : StringExecution.State mode)
    (entry : machine.principal.pc=Arithmetic.encodeNat mode (Listing8StateGeometry.region mode l).start) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8StateTrace.program mode (Listing8StateGeometry.region mode l) machine).map (StringStoreWrites.liftDword mode)) machine :=
  BoundedStoreRegions.interval mode _ _ _ _ machine (fun _ _ lower upper => Or.inr (Or.inl ⟨lower,upper⟩))
    (Listing8StateWrites.owned mode (Listing4EntryLayout.mainPC mode origin) (Listing8JumpLayout.jumpPC mode origin) _
      (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state)
      (Listing8GlobalMainBounds.state mode origin l t g node rule ctx)
      (Listing8GlobalMainBounds.state_cursor mode origin l t g node rule ctx) machine entry)

end SmcTuring.Appendix.Listing8GlobalSelectionRegions

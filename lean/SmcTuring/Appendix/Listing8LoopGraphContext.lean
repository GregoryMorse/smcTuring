module
public import SmcTuring.Appendix.Listing8GraphNextDirectionBounds

public section
namespace SmcTuring.Appendix.Listing8LoopGraphContext
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

/-- Static placement/resource certificates transfer to the actual logical
successor labels. No memory, image, value, readiness or trace is a premise. -/
theorem next (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (target : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Context mode origin (Listing8GraphMacroImages.nextLayout mode origin l g node rule target) t
      (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target :=
  ⟨rfl,rfl,Listing8GraphNextCopies.resources mode origin l t g node rule target ctx,
    Listing8GraphNextOwnerBounds.fields mode origin l t g node rule target ctx,
    Listing8GraphNextOwnerBounds.pointer_copies mode origin l t g node rule target ctx,
    Listing8GraphNextOwnerBounds.boot mode origin l t g node rule target ctx,
    Listing8GraphNextDirectionBounds.failure mode origin l t g node rule target ctx,
    Listing8GraphStep.native_bounds mode origin g node rule ctx.native⟩

end SmcTuring.Appendix.Listing8LoopGraphContext

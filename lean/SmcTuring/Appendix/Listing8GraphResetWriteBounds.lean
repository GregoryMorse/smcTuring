module
public import SmcTuring.Appendix.Listing8ResetWrites
public import SmcTuring.Appendix.Listing8GraphFieldWriteBounds

public section
namespace SmcTuring.Appendix.Listing8GraphResetWriteBounds
open Native Listing8Prototypes Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext

theorem placement (mode : Mode) (origin : Nat) (l : Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8ResetWrites.Placement mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8TableResetImage.region mode origin l (nodePC mode origin g g.halt) (table mode origin g)) := by
  rw [Listing8GraphReset.actual_region mode origin l t _ _ ctx.boot ctx.body,table_length]
  have upper:=Listing8LoopTailGeometry.input_before_end mode origin g
  have ending:=Listing8GraphReset.endpoint mode origin g.transitions
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals cases mode <;>
    simp [Listing8GraphReset.region,Listing8GraphLayout.input,Listing8GraphLayout.reset,
      Listing8GraphLayout.transition,Listing8FullTableImage.start,Listing8FailLayout.end_offset,Mode.wordBytes] at upper ending ⊢ <;> omega

end SmcTuring.Appendix.Listing8GraphResetWriteBounds

module
public import SmcTuring.Appendix.Listing9TailTemplateRegions
public import SmcTuring.Appendix.Listing8OriginalInterpreterWriteFrames
public import SmcTuring.Appendix.Listing9FullExecution

public section
namespace SmcTuring.Appendix.Listing9TailTemplateInitial
open Native Listing9PackedLayout Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem retained (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode (origin mode start) l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed size : Nat)
    (after : epilogue mode start g.transitions g.nodes≤observed) :
    ByteMemory.bytesAt (Listing9FullExecution.initial mode start l t g node rule memory seed).principal.memory observed size=
      ByteMemory.bytesAt (Listing9Image.memory mode start g.transitions g.nodes memory) observed size := by
  change ByteMemory.bytesAt (Listing8GraphBackedge.initial mode (origin mode start) l t g node rule
    (Listing9Image.memory mode start g.transitions g.nodes memory) seed).principal.memory observed size=_
  rw [Listing8LoopOriginalImage.initial_memory mode (origin mode start) l t g node rule ctx _ seed,
    Listing8LoopOriginalTailFrames.initial_window mode (origin mode start) l t g node rule ctx _ seed observed size after]

/-- All six/twelve late executable templates are derived from the original
Listing 9 image after the complete Listing 8 initialization overlays. -/
theorem original (mode : Mode) (start : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode (origin mode start) l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing9TailTemplates.Property mode start g.transitions g.nodes
      (Listing9FullExecution.initial mode start l t g node rule memory seed).principal.memory := by
  have ordered:=bounds_order mode start g.transitions g.nodes
  have current:=Listing9Image.epilogue_current mode start g.transitions g.nodes memory
  refine ⟨Listing9TailTemplateFields.initial_fixed mode start g.transitions g.nodes _
    (Listing9ExecutionImage.prologue_current mode start l t g node rule ctx memory seed) ?_,
    StringInitTemplates.initial mode _ 0 _ ?_,StringInitTemplates.initial mode _ (layout mode start g.transitions g.nodes).save _ ?_⟩
  · constructor
    · rw [retained mode start l t g node rule ctx memory seed (layout mode start g.transitions g.nodes).epilogue _
        (by change epilogue mode start g.transitions g.nodes≤epilogue mode start g.transitions g.nodes;exact Nat.le_refl _)]
      exact current.first
    · rw [retained mode start l t g node rule ctx memory seed _ _ (by unfold AccumulatorLayout.secondPC;change epilogue mode start g.transitions g.nodes≤epilogue mode start g.transitions g.nodes+_;omega)]
      exact current.second
    · rw [retained mode start l t g node rule ctx memory seed _ _ (by unfold AccumulatorLayout.thirdPC AccumulatorLayout.secondPC;change epilogue mode start g.transitions g.nodes≤epilogue mode start g.transitions g.nodes+_+_;omega)]
      exact current.third
  · rw [retained mode start l t g node rule ctx memory seed _ _ ordered.2.1]
    exact Listing9Image.save_current mode start g.transitions g.nodes memory
  · rw [retained mode start l t g node rule ctx memory seed _ _ (by dsimp [pointerOwner];omega)]
    exact Listing9Image.pointer_current mode start g.transitions g.nodes memory

end SmcTuring.Appendix.Listing9TailTemplateInitial

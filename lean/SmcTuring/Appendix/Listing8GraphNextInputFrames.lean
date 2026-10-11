module
public import SmcTuring.Appendix.Listing8GraphNextInput

public section
namespace SmcTuring.Appendix.Listing8GraphNextInputFrames
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem masks (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (helper : DwordLayout.Layout) (member : helper∈Listing8LiteralInput.distributionLayouts mode (nextLayout mode origin l g node rule target).input) :
    DwordCode.get (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory helper.destination=
      InputUpdate.mask (Listing8LiteralInput.chosen (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape) := by
  have separate : Listing8LiteralMaskTrace.Separate mode (nextLayout mode origin l g node rule target).input :=
    Listing8HeadGeometry.masks_separate mode l t ctx.body.state.head
  exact Listing8InputMaskEffects.destination_values mode (nextLayout mode origin l g node rule target).input
    (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
    (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
    ctx.resources.inputFits (Listing8InputBounds.masks mode (nextLayout mode origin l g node rule target)
      (Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx)) separate
    (Listing8GraphNextInputBounds.update mode origin l t g node rule target ctx) (Listing8GraphNextInputBounds.outside mode origin l t g node rule target ctx) _
    (Listing8GraphNextPointers.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextInputImage.current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.head_cursor mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.tape_symbol mode origin l t g node rule target ctx selected memory seed) helper member

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (after : Listing8FullTableImage.start mode origin≤observed)
    (tape : (nextLayout mode origin l g node rule target).sourceNode+10≤observed ∨ observed+count≤(nextLayout mode origin l g node rule target).sourceNode+6) :
    ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory observed count := by
  have fields:=Listing8LiteralComposition.field_bounds mode (nextLayout mode origin l g node rule target).input
  have before:=Listing8GraphCopyResources.input_before_table mode origin l t g node rule ctx
  change Listing8LiteralInput.endPC mode (nextLayout mode origin l g node rule target).input≤Listing8FullTableImage.start mode origin at before
  have disjoint : Listing8InputWindows.Outside mode (nextLayout mode origin l g node rule target).input observed count := by
    refine ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),tape,?_⟩
    intro helper member
    exact Or.inl (Nat.le_trans (Listing8GraphNextInputBounds.masks_before_table mode origin l t g node rule ctx helper member) after)
  exact Listing8InputWindows.window mode (nextLayout mode origin l g node rule target).input
    (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
    (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
    ctx.resources.inputFits (Listing8InputBounds.masks mode (nextLayout mode origin l g node rule target)
      (Listing8GraphNextInputBounds.fields mode origin l t g node rule target ctx))
    (Listing8GraphNextInputBounds.update mode origin l t g node rule target ctx) (Listing8GraphNextInputBounds.outside mode origin l t g node rule target ctx) _
    (Listing8GraphNextPointers.entry mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextInputImage.current mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.head_cursor mode origin l t g node rule target ctx selected memory seed)
    (Listing8GraphNextPointerFrames.tape_symbol mode origin l t g node rule target ctx selected memory seed) observed count disjoint

end SmcTuring.Appendix.Listing8GraphNextInputFrames

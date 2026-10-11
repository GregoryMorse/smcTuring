module
public import SmcTuring.Appendix.Listing8MainPrefixWrites
public import SmcTuring.Appendix.Listing8GraphInputWrites
public import SmcTuring.Appendix.Listing8MainGraphInput

public section
namespace SmcTuring.Appendix.Listing8MainInputWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets := Listing8PointerCopies.Targets
abbrev OldInput := Listing8MainInput.OldInput

theorem input_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (((Listing8LiteralComposition.program mode l.input (values mode origin g node rule).rule
        (values mode origin g node rule).tape (values mode origin g node rule).fresh).map (StringMixed.canonical mode)).map
          (StringStoreWrites.liftDword mode))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) := by
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated entry
  have bounds := Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  exact Listing8LiteralInputWrites.mask_canonical_owned mode origin _ l.input
    (Listing8GraphInputWriteBounds.placement mode origin l t g node rule ctx)
    _ _ old.pending _ old.mask ctx.resources.inputFits
    (Listing8InputBounds.masks mode l bounds.input.prefixBounds.fields)
    (Listing8InputBounds.update mode l t bounds.input.prefixBounds.fields bounds.input.prefixBounds.joined ctx.resources)
    (Listing8InputBounds.outside mode l t bounds.input.prefixBounds.fields bounds.input.prefixBounds.joined ctx.resources) _
    (Listing8MainPrefix.entry mode l t _ bounds.input.prefixBounds state entry.entry entry.forward image.prefixCurrent)
    (Listing8MainInputImage.current mode l t _ old bounds.input state entry.entry entry.forward image)
    (Listing8MainPrefixFrames.head_cursor mode l t _ bounds.input.prefixBounds state entry.entry entry.forward image.prefixCurrent)

/-- The repeated 101/118 instruction body prefix owns every complete
architectural store, including arbitrary old pending/mask values. -/
theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8MainInput.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated entry
  rw [Listing8MainInput.program,List.map_append]
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ state (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state)
  · exact StringDwordWritesBridge.trace mode (Listing8MainPrefix.trace mode l t _
      (Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds state entry.entry entry.forward image.prefixCurrent)
  · exact Listing8MainPrefixWrites.owned mode origin l t g node rule ctx state entry.entry entry.forward image.prefixCurrent
  · exact input_owned mode origin l t g node rule ctx old state entry

theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      ((Listing8MainInput.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8MainInput.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated entry
  exact ⟨StringDwordWritesBridge.trace mode (Listing8MainInput.trace mode l t _ old
    (Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx) state entry.entry entry.forward image),
    owned mode origin l t g node rule ctx old state entry⟩

end SmcTuring.Appendix.Listing8MainInputWrites

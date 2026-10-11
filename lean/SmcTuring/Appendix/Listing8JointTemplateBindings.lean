module
public import SmcTuring.Appendix.Listing8InputJointTemplates
public import SmcTuring.Appendix.Listing8RetargetTapeTemplates

public section
namespace SmcTuring.Appendix.Listing8JointTemplateBindings
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets := Listing8PointerCopies.Targets
abbrev OldInput := Listing8MainInput.OldInput

/-- Present original/maintained main bytes derive the input entry and image.
Every literal input packet window is valid at every actual input prefix;
the complete main trace, endpoint and selected tape output are retained. -/
theorem input (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput)
    (b : Listing8MainInput.Bounds mode l t v) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (forward : state.backwards=false)
    (current : Listing8MainInput.Current mode l t v old state.principal.memory) :
    StringStack.Trace mode state
      (((Listing8MainInput.program mode l t v).map StringControl.Form.previous).map StringStack.Form.previous)
      (Listing8MainInput.finish mode l t v state) ∧
    (Listing8MainInput.finish mode l t v state).principal.pc=Arithmetic.encodeNat mode (Listing8LiteralInput.endPC mode l.input) ∧
    DwordCode.get (Listing8MainInput.finish mode l t v state).principal.memory (l.input.head+6)=
      (if Listing8LiteralInput.chosen v.rule v.tape then v.fresh else v.tape) ∧
    StringTemplateStates.Run mode (fun reached =>
      ∀ window∈MixedTemplateGeometry.windows mode l.input.start (Listing8LiteralComposition.program mode l.input v.rule v.tape v.fresh),
        Listing8InputJointTemplates.ValidWindow mode window reached.principal.memory)
      (((Listing8LiteralComposition.program mode l.input v.rule v.tape v.fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode))
      (Listing8MainPrefix.finish mode l t v state) := by
  have fields := b.input.prefixBounds.fields
  have masks := Listing8InputBounds.masks mode l fields
  have update := Listing8InputBounds.update mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have outside := Listing8InputBounds.outside mode l t fields b.input.prefixBounds.joined b.input.prefixBounds.resources
  have atInput := Listing8MainPrefix.entry mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  have image := Listing8MainInputImage.current mode l t v old b.input state entry forward current
  have cursor := Listing8MainPrefixFrames.head_cursor mode l t v b.input.prefixBounds state entry forward current.prefixCurrent
  exact ⟨Listing8MainInput.stack_trace mode l t v old b state entry forward current,
    Listing8MainInput.endpoint mode l t v old b state entry forward current,
    Listing8MainInput.tape_value mode l t v old b state entry forward current,
    Listing8InputJointTemplates.all_windows mode l.input v.rule v.tape old.pending v.fresh old.mask
      b.input.prefixBounds.resources.inputFits masks update outside _ atInput image cursor⟩

theorem graph_input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Listing8SourceGraph.Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      ∀ window∈MixedTemplateGeometry.windows mode l.input.start
        (Listing8LiteralComposition.program mode l.input (Listing8SourceGraph.values mode origin g node rule).rule
          (Listing8SourceGraph.values mode origin g node rule).tape (Listing8SourceGraph.values mode origin g node rule).fresh),
        Listing8InputJointTemplates.ValidWindow mode window reached.principal.memory)
      (((Listing8LiteralComposition.program mode l.input (Listing8SourceGraph.values mode origin g node rule).rule
        (Listing8SourceGraph.values mode origin g node rule).tape (Listing8SourceGraph.values mode origin g node rule).fresh).map
          (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode))
      (Listing8MainPrefix.finish mode l t (Listing8SourceGraph.values mode origin g node rule) state) := by
  have image := Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated entry
  exact (input mode l t _ old (Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx)
    state entry.entry entry.forward image).2.2.2

end SmcTuring.Appendix.Listing8JointTemplateBindings

module
public import SmcTuring.Appendix.Listing8MainGraphInputNodes
public import SmcTuring.Appendix.Listing8MainInputMacroWindows

public section
namespace SmcTuring.Appendix.Listing8MainGraphInput
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem correct (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      (((Listing8MainInput.program mode l t (values mode origin g node rule)).map StringControl.Form.previous).map StringStack.Form.previous)
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state) ∧
    (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.pc=Arithmetic.encodeNat mode (Listing8LiteralInput.endPC mode l.input) ∧
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated entry
  have actual:=Listing8MainGraphInputNodes.source_graph mode origin l t g node rule ctx old state entry
  exact ⟨Listing8MainGraphImage.trace mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated
    (Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx) entry,
    Listing8MainInput.endpoint mode l t _ old (Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx)
      state entry.entry entry.forward image,actual.1,actual.2⟩

theorem tape_symbol (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (query : Fin g.nodes) :
    DwordCode.get (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory (nodePC mode origin g query+6)=
      ((Listing8GraphStep.updated g node rule).tape query).symbol := by
  have actual:=node_values mode (nodePC mode origin g query) (Listing8GraphBodyNodes.symbol g node rule query)
    (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).back))
    (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).forward)) _ (by
      simpa only [node_length,Listing8NodeBlock.bytes,Listing8GraphNodeImage.value,Listing8GraphStep.updated,nodePC] using
        Listing8MainGraphInputNodes.current mode origin l t g node rule ctx old state entry query)
  exact actual.1

theorem neighbors (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (query : Fin g.nodes) :
    MixedMemory.getWord mode (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory
      (pointerField mode (backEntry mode (nodePC mode origin g query)))=Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).back) ∧
    MixedMemory.getWord mode (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory
      (pointerField mode (forwardEntry mode (nodePC mode origin g query)))=Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).forward) := by
  have actual:=node_values mode (nodePC mode origin g query) (Listing8GraphBodyNodes.symbol g node rule query)
    (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).back))
    (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).forward)) _ (by
      simpa only [node_length,Listing8NodeBlock.bytes,Listing8GraphNodeImage.value,Listing8GraphStep.updated,nodePC] using
        Listing8MainGraphInputNodes.current mode origin l t g node rule ctx old state entry query)
  exact actual.2

/-- Both immutable copy-macro header/suffix pairs and the full current
head-copy packet are available after the general actual input phase. -/
theorem macro_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory l.start
      (StringMacroLayout.bytes mode (nodeParams mode l)).length=StringMacroLayout.bytes mode (nodeParams mode l) ∧
    (∀ second : Bool,
      ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory
        (Listing8MainInputMacroWindows.params mode l second).start (StringCodec.fieldOffset mode)=
        StringInit.leading mode (Listing8MainInputMacroWindows.params mode l second).start ∧
      ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory
        ((Listing8MainInputMacroWindows.params mode l second).start+StringCodec.initialSize mode)
        (StringMacroSource.tailBytes mode (Listing8MainInputMacroWindows.params mode l second)).length=
        StringMacroSource.tailBytes mode (Listing8MainInputMacroWindows.params mode l second)) := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated entry
  have b:=Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx
  exact ⟨Listing8MainInputMacroWindows.node_current mode l t _ old b state entry.entry entry.forward image,
    fun second => ⟨Listing8MainInputMacroWindows.header mode l t _ old b state entry.entry entry.forward image second,
      Listing8MainInputMacroWindows.tail mode l t _ old b state entry.entry entry.forward image second⟩⟩

end SmcTuring.Appendix.Listing8MainGraphInput

module
public import SmcTuring.Appendix.Listing8MainInput
public import SmcTuring.Appendix.Listing8GraphInputContext

public section
namespace SmcTuring.Appendix.Listing8MainGraphImage
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInputImage.OldInput

/-- A graph-labelled present main-entry contract. Full graph/table bytes,
immutable macro fragments, actual cursor words and past input fields are
observations of this state, rather than assertions about a future state. -/
structure Current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode) : Prop where
  entry : state.principal.pc=Arithmetic.encodeNat mode l.start
  forward : state.backwards=false
  nodeMacro : Listing8MainCopyImage.MacroCurrent mode (nodeParams mode l) state.principal.memory
  ruleMacro : Listing8MainCopyImage.MacroCurrent mode (transitionParams mode l) state.principal.memory
  patches : ByteMemory.bytesAt state.principal.memory (patchStart mode l) (patchBytes mode l).length=patchBytes mode l
  helpers : ByteMemory.bytesAt state.principal.memory (codeEnd mode l) (Listing8PointerCopies.bytes mode l t).length=Listing8PointerCopies.bytes mode l t
  input : Listing8InputMask.Intact mode l.input old.rule old.tape old.pending old.fresh old.mask state.principal.memory
  nodes : Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
    (Listing8GraphNodeImage.declarations mode origin g) state.principal.memory
  rules : Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) state.principal.memory

theorem source_packets (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (current : Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt state.principal.memory l.sourceNode (nodeSpan mode)=sourceNodeBytes mode l (values mode origin g node rule) ∧
    ByteMemory.bytesAt state.principal.memory l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l (values mode origin g node rule) := by
  constructor
  · have selected:=Listing8NodeTable.selected_current mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin g) node.val (Listing8GraphNodeImage.value mode origin g node)
      (Listing8GraphNodeImage.lookup mode origin g node) _ current.nodes
    simpa only [sourceNodeBytes,values,Listing8NodeBlock.bytes,Listing8GraphNodeImage.value,nodeLocated,Listing8NodeTable.entryPC,nodePC,Listing8GraphLayout.node] using selected
  · have selected:=Listing8TransitionTable.selected_current mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      rule.val (values mode origin g g.halt rule) (lookup mode origin g rule) _ current.rules
    simpa only [sourceTransitionBytes,values,ruleLocated,Listing8TransitionTable.entryPC,rulePC,Listing8GraphLayout.transition] using selected

theorem input_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (current : Current mode origin l t g node rule old state) :
    Listing8MainInput.Current mode l t (values mode origin g node rule) old state.principal.memory := by
  have packets:=source_packets mode origin l t g node rule old state nodeLocated ruleLocated current
  exact ⟨⟨⟨current.nodeMacro,current.ruleMacro,current.patches,packets.1,packets.2⟩,current.helpers⟩,current.input⟩

/-- The arbitrary-entry trace is instantiated from the complete current
logical graph and source bindings, without a future copy/value hypothesis. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8MainInput.Bounds mode l t (values mode origin g node rule))
    (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state
      (((Listing8MainInput.program mode l t (values mode origin g node rule)).map StringControl.Form.previous).map StringStack.Form.previous)
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state) :=
  Listing8MainInput.stack_trace mode l t _ old b state current.entry current.forward
    (input_current mode origin l t g node rule old state nodeLocated ruleLocated current)

theorem tape_value (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (state : StringExecution.State mode)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (b : Listing8MainInput.Bounds mode l t (values mode origin g node rule))
    (current : Current mode origin l t g node rule old state) :
    DwordCode.get (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory (l.input.head+6)=
      if (g.rules rule).symbol=(g.tape node).symbol then (g.rules rule).fresh else (g.tape node).symbol := by
  have actual:=Listing8MainInput.tape_value mode l t _ old b state current.entry current.forward
    (input_current mode origin l t g node rule old state nodeLocated ruleLocated current)
  change DwordCode.get (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory (l.input.head+6)=
    (if Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol then (g.rules rule).fresh else (g.tape node).symbol) at actual
  by_cases same : (g.rules rule).symbol=(g.tape node).symbol
  · have chosen:=(Listing8GraphRun.chosen_iff g node rule).mpr same
    rw [if_pos same]
    simpa only [chosen,ite_true] using actual
  · have chosen : Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol=false := by
      cases h : Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol
      · rfl
      · exact False.elim (same ((Listing8GraphRun.chosen_iff g node rule).mp h))
    rw [if_neg same]
    simpa only [chosen,Bool.false_eq_true,ite_false] using actual

end SmcTuring.Appendix.Listing8MainGraphImage

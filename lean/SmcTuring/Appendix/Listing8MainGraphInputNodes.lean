module
public import SmcTuring.Appendix.Listing8MainGraphPrefix

public section
namespace SmcTuring.Appendix.Listing8MainGraphInputNodes
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem before_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (query : Fin g.nodes) :
    ByteMemory.bytesAt (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory
      (nodePC mode origin g query) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g query) (Listing8GraphNodeImage.value mode origin g query) :=
  Listing8NodeTable.selected_current mode (Listing8GraphLayout.input mode origin g.transitions)
    (Listing8GraphNodeImage.declarations mode origin g) query.val _ (Listing8GraphNodeImage.lookup mode origin g query) _
    (Listing8MainGraphPrefix.source_graph mode origin l t g node rule ctx old state entry).1

/-- The selected complete node packet is rebuilt after the actual generic
input update from its retained headers/neighbors and derived new tape symbol. -/
theorem source_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory
      (nodePC mode origin g node) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g node) (Listing8GraphNodeImage.value mode origin (Listing8GraphStep.updated g node rule) node) := by
  have packet:=before_current mode origin l t g node rule ctx old state entry node
  have pieces:=Listing8LiveNodePacket.windows mode (nodePC mode origin g node) (g.tape node).symbol
    (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).back)) (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).forward)) _ packet
  have after:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  have header : ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory (nodePC mode origin g node) 6=
      Listing8LiveNodePacket.headerBytes mode (nodePC mode origin g node) := by
    rw [Listing8MainGraphPrefix.input_window mode origin l t g node rule ctx old state entry _ _ after
      (Or.inr (by rw [ctx.nodeLocated]))]
    exact pieces.1
  have pointers : ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory (nodePC mode origin g node+10) (2*pointerSpan mode)=
      pointerBytes mode (backEntry mode (nodePC mode origin g node)) (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).back))++
      pointerBytes mode (forwardEntry mode (nodePC mode origin g node)) (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).forward)) := by
    rw [Listing8MainGraphPrefix.input_window mode origin l t g node rule ctx old state entry _ _ (by omega)
      (Or.inl (by rw [ctx.nodeLocated]))]
    exact pieces.2
  have symbol:=Listing8MainInput.tape_value mode l t (values mode origin g node rule) old
    (Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx) state entry.entry entry.forward
    (Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated entry)
  rw [ctx.body.state.head.input.fields.headLabel,ctx.nodeLocated] at symbol
  have assembled:=Listing8LiveNodePacket.current mode _ _ _ _ _ header pointers symbol
  calc
    _ = nodeBytes mode (nodePC mode origin g node)
      (if Listing8LiteralInput.chosen (values mode origin g node rule).rule (values mode origin g node rule).tape
        then (values mode origin g node rule).fresh else (values mode origin g node rule).tape)
      (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).back))
      (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).forward)) := assembled
    _ = _ := by
      simp only [Listing8NodeBlock.bytes,Listing8GraphNodeImage.value,Listing8GraphStep.updated,
        Listing8GraphBodyNodes.symbol,eq_self,ite_true,values,nodePC]
      rfl

theorem other_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (query : Fin g.nodes) (different : query≠node) :
    ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory (nodePC mode origin g query) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g query) (Listing8GraphNodeImage.value mode origin (Listing8GraphStep.updated g node rule) query) := by
  have outside : l.sourceNode+10≤nodePC mode origin g query ∨ nodePC mode origin g query+nodeSpan mode≤l.sourceNode+6 := by
    rw [ctx.nodeLocated]
    have distinct : query.val≠node.val := by intro same;exact different (Fin.ext same)
    have large : 10≤nodeSpan mode := by unfold nodeSpan;omega
    rcases Nat.lt_or_gt_of_ne distinct with before | later
    · have apart:=Listing8GraphLayout.nodes_apart mode origin g.transitions query.val node.val before
      change nodePC mode origin g query+nodeSpan mode≤nodePC mode origin g node at apart
      right;omega
    · have apart:=Listing8GraphLayout.nodes_apart mode origin g.transitions node.val query.val later
      change nodePC mode origin g node+nodeSpan mode≤nodePC mode origin g query at apart
      left;omega
  rw [Listing8MainGraphPrefix.input_window mode origin l t g node rule ctx old state entry _ _
    (Listing8GraphOwnerBounds.node_after_table mode origin g query) outside,before_current mode origin l t g node rule ctx old state entry query]
  simp only [Listing8NodeBlock.bytes,Listing8GraphNodeImage.value,Listing8GraphStep.updated,
    Listing8GraphBodyNodes.symbol,ite_eq_right different,nodePC]

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state)
    (query : Fin g.nodes) :
    ByteMemory.bytesAt (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory (nodePC mode origin g query) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g query) (Listing8GraphNodeImage.value mode origin (Listing8GraphStep.updated g node rule) query) := by
  by_cases same : query=node
  · subst query;exact source_current mode origin l t g node rule ctx old state entry
  · exact other_current mode origin l t g node rule ctx old state entry query same

theorem nodes_initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory := by
  apply Listing8LiveNodePacket.initial_from_packets
  intro index item found
  have within : index<g.nodes := by
    have small:=List.getElem?_eq_some_iff.mp found |>.1
    rw [Listing8GraphNodeImage.length] at small
    exact small
  have actual:=Listing8GraphNodeImage.lookup mode origin (Listing8GraphStep.updated g node rule) ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst item
  exact current mode origin l t g node rule ctx old state entry ⟨index,within⟩

theorem table_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have before:=Listing8GraphLayout.table_before_input mode origin g.transitions
  have nodeAfter:=Listing8GraphLayout.node_lower mode origin g.transitions node.val
  change Listing8GraphLayout.input mode origin g.transitions≤nodePC mode origin g node at nodeAfter
  have extent : Listing8FullTableImage.start mode origin+
      (Listing8TransitionTable.bytes mode (Listing8FullTableImage.start mode origin) (table mode origin g)).length=Listing8GraphLayout.reset mode origin g.transitions := by
    rw [Listing8TransitionTable.bytes_length,table_length];rfl
  rw [Listing8TransitionTable.Initial,Listing8MainGraphPrefix.input_window mode origin l t g node rule ctx old state entry
    _ _ (Nat.le_refl _) (Or.inr (by rw [extent,ctx.nodeLocated];omega))]
  exact (Listing8MainGraphPrefix.source_graph mode origin l t g node rule ctx old state entry).2

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8MainInput.finish mode l t (values mode origin g node rule) state).principal.memory :=
  ⟨nodes_initial mode origin l t g node rule ctx old state entry,table_current mode origin l t g node rule ctx old state entry⟩

end SmcTuring.Appendix.Listing8MainGraphInputNodes

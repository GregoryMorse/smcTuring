module
public import SmcTuring.Appendix.Listing8GraphInputInitial

public section
namespace SmcTuring.Appendix.Listing8GraphBodyNodes
open Native Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext
@[expose] def symbol (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (query : Fin g.nodes) :=
  if query=node then (if Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol
    then (g.rules rule).fresh else (g.tape node).symbol) else (g.tape query).symbol
@[expose] def value (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (query : Fin g.nodes) :=
  {Listing8GraphNodeImage.value mode origin g query with symbol:=symbol g node rule query}
@[expose] def declarations (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  List.ofFn (value mode origin g node rule)
theorem length (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (declarations mode origin g node rule).length=g.nodes := List.length_ofFn
theorem lookup (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (query : Fin g.nodes) :
    (declarations mode origin g node rule)[query.val]?=some (value mode origin g node rule query) := by
  simp only [declarations,List.getElem?_ofFn,query.isLt,dite_true]

theorem after_node (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (query : Fin g.nodes) (offset : Nat) :
    Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin))+5≤nodePC mode origin g query+offset := by
  have before:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
    (Listing8GraphLayout.node_lower mode origin g.transitions query.val)
  change _≤nodePC mode origin g query at before
  omega
theorem window (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat)
    (after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin))+5≤observed)
    (outside : l.sourceNode+10≤observed ∨ observed+count≤l.sourceNode+6) :
    ByteMemory.bytesAt (bodyEnd mode origin l t g node rule memory seed).principal.memory observed count=
      ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory) observed count :=
  Listing8LateFrames.after_failure mode l t (values mode origin g node rule) _ _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body (extra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed) observed count after outside

/-- The selected node's new immediate is recovered from actual execution;
its instruction header and both complete reader packets are framed. -/
theorem source_current (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (bodyEnd mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g node) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g node) (value mode origin g node rule node) := by
  have packet:=Listing8GraphInputInitial.source_current mode origin l t g node rule ctx memory
  have pieces:=Listing8LiveNodePacket.windows mode (nodePC mode origin g node) (g.tape node).symbol
    (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).back))
    (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).forward)) _ packet
  have header : ByteMemory.bytesAt (bodyEnd mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g node) 6=
      Listing8LiveNodePacket.headerBytes mode (nodePC mode origin g node) := by
    rw [window mode origin l t g node rule ctx memory seed (nodePC mode origin g node) 6
      (by simpa only [Nat.add_zero] using after_node mode origin l t g node rule ctx node 0)
      (Or.inr (by rw [ctx.nodeLocated]))]
    exact pieces.1
  have pointers : ByteMemory.bytesAt (bodyEnd mode origin l t g node rule memory seed).principal.memory
      (nodePC mode origin g node+10) (2*pointerSpan mode)=
      pointerBytes mode (backEntry mode (nodePC mode origin g node)) (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).back))++
      pointerBytes mode (forwardEntry mode (nodePC mode origin g node)) (Arithmetic.encodeNat mode (nodePC mode origin g (g.tape node).forward)) := by
    rw [window mode origin l t g node rule ctx memory seed _ _ (after_node mode origin l t g node rule ctx node 10)
      (Or.inl (by rw [ctx.nodeLocated]))]
    exact pieces.2
  have tape : DwordCode.get (bodyEnd mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g node+6)=
      if Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol then (g.rules rule).fresh else (g.tape node).symbol := by
    rw [←ctx.nodeLocated]
    exact Listing8GlobalBootValues.tape mode origin l t (values mode origin g node rule) _ ctx.resources
      (owners mode origin l t g node rule ctx) ctx.copies ctx.body _ seed
  change ByteMemory.bytesAt _ _ (nodeSpan mode)=nodeBytes mode _ (symbol g node rule node) _ _
  simp only [symbol]
  exact Listing8LiveNodePacket.current mode _ _ _ _ _ header pointers tape

theorem other_current (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.nodes) (different : query≠node) :
    ByteMemory.bytesAt (bodyEnd mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g query) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g query) (value mode origin g node rule query) := by
  have outside : l.sourceNode+10≤nodePC mode origin g query ∨ nodePC mode origin g query+nodeSpan mode≤l.sourceNode+6 := by
    rw [ctx.nodeLocated]
    have distinct : query.val≠node.val := by intro same;exact different (Fin.ext same)
    have large : 10≤nodeSpan mode := by cases mode <;> decide
    rcases Nat.lt_or_gt_of_ne distinct with before | later
    · have separate:=Listing8GraphLayout.nodes_apart mode origin g.transitions query.val node.val before
      change nodePC mode origin g query+nodeSpan mode≤nodePC mode origin g node at separate
      right;omega
    · have separate:=Listing8GraphLayout.nodes_apart mode origin g.transitions node.val query.val later
      change nodePC mode origin g node+nodeSpan mode≤nodePC mode origin g query at separate
      left;omega
  rw [window mode origin l t g node rule ctx memory seed (nodePC mode origin g query) (nodeSpan mode)
    (by simpa only [Nat.add_zero] using after_node mode origin l t g node rule ctx query 0) outside,
    Listing8GraphInputInitial.other_current mode origin l t g node rule ctx memory query different]
  simp only [Listing8NodeBlock.bytes,Listing8GraphNodeImage.value,value,symbol,ite_eq_right different]
theorem current (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.nodes) :
    ByteMemory.bytesAt (bodyEnd mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g query) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g query) (value mode origin g node rule query) := by
  by_cases same : query=node
  · subst query;exact source_current mode origin l t g node rule ctx memory seed
  · exact other_current mode origin l t g node rule ctx memory seed query same
end SmcTuring.Appendix.Listing8GraphBodyNodes

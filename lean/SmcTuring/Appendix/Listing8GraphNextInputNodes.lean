module
public import SmcTuring.Appendix.Listing8GraphNextInputFrames

public section
namespace SmcTuring.Appendix.Listing8GraphNextInputNodes
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def graph (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) :=
  Listing8GraphStep.updated (Listing8GraphStep.updated g node rule) (Listing8GraphStep.nextNode g node rule) target

theorem before_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.nodes) :
    ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory
      (nodePC mode origin g query) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g query) (Listing8GraphNodeImage.value mode origin (Listing8GraphStep.updated g node rule) query) :=
  Listing8NodeTable.selected_current mode (Listing8GraphLayout.input mode origin g.transitions)
    (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule)) query.val _
    (Listing8GraphNodeImage.lookup mode origin (Listing8GraphStep.updated g node rule) query) _
    (Listing8GraphNextPointerFrames.source_graph mode origin l t g node rule target ctx selected memory seed).1

theorem source_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory
      (nodePC mode origin g (Listing8GraphStep.nextNode g node rule)) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g (Listing8GraphStep.nextNode g node rule))
        (Listing8GraphNodeImage.value mode origin (graph g node rule target) (Listing8GraphStep.nextNode g node rule)) := by
  let head:=Listing8GraphStep.nextNode g node rule
  let old:=Listing8GraphStep.updated g node rule
  have packet:=before_current mode origin l t g node rule target ctx selected memory seed head
  have pieces:=Listing8LiveNodePacket.windows mode (nodePC mode origin g head) (old.tape head).symbol
    (Arithmetic.encodeNat mode (nodePC mode origin g (old.tape head).back)) (Arithmetic.encodeNat mode (nodePC mode origin g (old.tape head).forward)) _ packet
  have after:=Listing8GraphOwnerBounds.node_after_table mode origin g head
  have header : ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory (nodePC mode origin g head) 6=
      Listing8LiveNodePacket.headerBytes mode (nodePC mode origin g head) := by
    rw [Listing8GraphNextInputFrames.window mode origin l t g node rule target ctx selected memory seed _ _ after (Or.inr (by change nodePC mode origin g head+6≤nodePC mode origin g head+6;omega))]
    exact pieces.1
  have pointers : ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory (nodePC mode origin g head+10) (2*pointerSpan mode)=
      pointerBytes mode (backEntry mode (nodePC mode origin g head)) (Arithmetic.encodeNat mode (nodePC mode origin g (old.tape head).back))++
      pointerBytes mode (forwardEntry mode (nodePC mode origin g head)) (Arithmetic.encodeNat mode (nodePC mode origin g (old.tape head).forward)) := by
    rw [Listing8GraphNextInputFrames.window mode origin l t g node rule target ctx selected memory seed _ _ (by omega) (Or.inl (by change nodePC mode origin g head+10≤nodePC mode origin g head+10;omega))]
    exact pieces.2
  have symbol:=Listing8GraphNextInput.tape_value mode origin l t g node rule target ctx selected memory seed
  have assembled:=Listing8LiveNodePacket.current mode _ _ _ _ _ header pointers symbol
  calc
    _ = nodeBytes mode (nodePC mode origin g head)
      (if Listing8LiteralInput.chosen (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
        then (liveValues mode origin g node rule target).fresh else (liveValues mode origin g node rule target).tape)
      (Arithmetic.encodeNat mode (nodePC mode origin g (old.tape head).back))
      (Arithmetic.encodeNat mode (nodePC mode origin g (old.tape head).forward)) := assembled
    _ = _ := by
      simp only [Listing8NodeBlock.bytes,Listing8GraphNodeImage.value,graph,Listing8GraphStep.updated,
        Listing8GraphBodyNodes.symbol,eq_self,ite_true,head,old,liveValues,values,nodePC]
      rfl

theorem other_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (query : Fin g.nodes) (different : query≠Listing8GraphStep.nextNode g node rule) :
    ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory (nodePC mode origin g query) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g query) (Listing8GraphNodeImage.value mode origin (graph g node rule target) query) := by
  have outside : (nextLayout mode origin l g node rule target).sourceNode+10≤nodePC mode origin g query ∨
      nodePC mode origin g query+nodeSpan mode≤(nextLayout mode origin l g node rule target).sourceNode+6 := by
    change nodePC mode origin g (Listing8GraphStep.nextNode g node rule)+10≤nodePC mode origin g query ∨
      nodePC mode origin g query+nodeSpan mode≤nodePC mode origin g (Listing8GraphStep.nextNode g node rule)+6
    have distinct : query.val≠(Listing8GraphStep.nextNode g node rule).val := by intro same;exact different (Fin.ext same)
    have large : 10≤nodeSpan mode := by unfold nodeSpan;omega
    rcases Nat.lt_or_gt_of_ne distinct with before | later
    · have apart:=Listing8GraphLayout.nodes_apart mode origin g.transitions query.val (Listing8GraphStep.nextNode g node rule).val before
      change nodePC mode origin g query+nodeSpan mode≤nodePC mode origin g (Listing8GraphStep.nextNode g node rule) at apart
      right;omega
    · have apart:=Listing8GraphLayout.nodes_apart mode origin g.transitions (Listing8GraphStep.nextNode g node rule).val query.val later
      change nodePC mode origin g (Listing8GraphStep.nextNode g node rule)+nodeSpan mode≤nodePC mode origin g query at apart
      left;omega
  rw [Listing8GraphNextInputFrames.window mode origin l t g node rule target ctx selected memory seed _ _
    (Listing8GraphOwnerBounds.node_after_table mode origin g query) outside,before_current mode origin l t g node rule target ctx selected memory seed query]
  simp only [Listing8NodeBlock.bytes,Listing8GraphNodeImage.value,graph,Listing8GraphStep.updated,Listing8GraphBodyNodes.symbol,ite_eq_right different,nodePC]

theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.nodes) :
    ByteMemory.bytesAt (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory (nodePC mode origin g query) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g query) (Listing8GraphNodeImage.value mode origin (graph g node rule target) query) := by
  by_cases same : query=Listing8GraphStep.nextNode g node rule
  · subst query;exact source_current mode origin l t g node rule target ctx selected memory seed
  · exact other_current mode origin l t g node rule target ctx selected memory seed query same

theorem nodes_initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (graph g node rule target))
      (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory := by
  apply Listing8LiveNodePacket.initial_from_packets
  intro index item found
  have within : index<g.nodes := by
    have small:=List.getElem?_eq_some_iff.mp found |>.1
    rw [Listing8GraphNodeImage.length] at small
    exact small
  have actual:=Listing8GraphNodeImage.lookup mode origin (graph g node rule target) ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst item
  exact current mode origin l t g node rule target ctx selected memory seed ⟨index,within⟩

theorem table_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory := by
  have before:=Listing8GraphLayout.table_before_input mode origin g.transitions
  have nodeAfter:=Listing8GraphLayout.node_lower mode origin g.transitions (Listing8GraphStep.nextNode g node rule).val
  have extent : Listing8FullTableImage.start mode origin+
      (Listing8TransitionTable.bytes mode (Listing8FullTableImage.start mode origin) (table mode origin g)).length=
      Listing8GraphLayout.reset mode origin g.transitions := by
    rw [Listing8TransitionTable.bytes_length,table_length]
    rfl
  rw [Listing8TransitionTable.Initial,Listing8GraphNextInputFrames.window mode origin l t g node rule target ctx selected memory seed
    _ _ (Nat.le_refl _) (Or.inr (by
      rw [extent]
      change Listing8GraphLayout.reset mode origin g.transitions≤nodePC mode origin g (Listing8GraphStep.nextNode g node rule)+6
      change Listing8GraphLayout.input mode origin g.transitions≤nodePC mode origin g (Listing8GraphStep.nextNode g node rule) at nodeAfter
      omega))]
  exact (Listing8GraphNextPointerFrames.source_graph mode origin l t g node rule target ctx selected memory seed).2

theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (graph g node rule target))
      (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (Listing8GraphNextInput.finish mode origin l t g node rule target memory seed).principal.memory :=
  ⟨nodes_initial mode origin l t g node rule target ctx selected memory seed,table_current mode origin l t g node rule target ctx selected memory seed⟩

end SmcTuring.Appendix.Listing8GraphNextInputNodes

module
public import SmcTuring.Appendix.Listing8GraphNextCopies

public section
namespace SmcTuring.Appendix.Listing8GraphNextCopyFrames
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextCopies
abbrev Targets:=Listing8PointerCopies.Targets

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat) (after : codeEnd mode l≤observed) :
    ByteMemory.bytesAt (finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  have dests:=destinations mode (nextLayout mode origin l g node rule target)
  have related:=dests.2
  change (nodeParams mode (nextLayout mode origin l g node rule target)).destination+nodeSpan mode=
      (transitionParams mode (nextLayout mode origin l g node rule target)).destination ∧
    (transitionParams mode (nextLayout mode origin l g node rule target)).destination+transitionSpan mode=codeEnd mode l at related
  rw [effect mode origin l t g node rule target ctx selected memory seed,
    byte_frame _ _ _ _ _ (Or.inl (by simp only [sourceTransitionBytes,transition_length];omega)),
    byte_frame _ _ _ _ _ (Or.inl (by simp only [sourceNodeBytes,node_length];omega))]
theorem source_graph (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated g node rule))
      (finish mode origin l t g node rule target memory seed).principal.memory ∧
    Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g)
      (finish mode origin l t g node rule target memory seed).principal.memory := by
  have codeBefore:=Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have inputBefore:=Nat.le_trans (Listing8GraphLayout.transition_lower mode origin g.transitions)
    (Listing8GraphLayout.table_before_input mode origin g.transitions)
  constructor
  · rw [Listing8NodeTable.Initial,window mode origin l t g node rule target ctx selected memory seed _ _ (Nat.le_trans codeBefore inputBefore)]
    exact Listing8GraphBackedgeSources.nodes_initial mode origin l t g node rule ctx memory seed
  · rw [Listing8TransitionTable.Initial,window mode origin l t g node rule target ctx selected memory seed _ _ codeBefore]
    exact Listing8GraphBackedgeSources.table_current mode origin l t g node rule ctx memory seed
theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc=Arithmetic.encodeNat mode (patchStart mode l) ∧
    (finish mode origin l t g node rule target memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule target memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule target memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule target memory seed).backwards=false ∧
    (finish mode origin l t g node rule target memory seed).principal.carry=false := by
  have prior:=Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
  rw [effect mode origin l t g node rule target ctx selected memory seed]
  exact ⟨rfl,prior.2.1,prior.2.2.1,prior.2.2.2.1,prior.2.2.2.2.1,rfl⟩
theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule target memory seed).principal.pc.toNat=origin+(if mode=.x86 then 199 else 330) := by
  have resource:=resources mode origin l t g node rule target ctx
  have capacity : patchStart mode l<2^(8*mode.wordBytes) := resource.transition.codeFits
  rw [(registers mode origin l t g node rule target ctx selected memory seed).1,
    Arithmetic.encode_nat_toNat mode _ capacity,(Listing8Initializer.code_geometry mode l).2.1,ctx.boot.packed]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false,Listing4EntryLayout.mainPC,Listing4EntryLayout.size] <;> omega

end SmcTuring.Appendix.Listing8GraphNextCopyFrames

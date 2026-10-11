module
public import SmcTuring.Appendix.Listing8GraphTableBounds
public import SmcTuring.Appendix.Listing8GraphNodeImage
public import SmcTuring.Appendix.Listing8GraphOwnerBounds

public section
namespace SmcTuring.Appendix.Listing8GraphRun
open Native Listing8SourceGraph

/-- A halt edge in the initial logical graph, rather than a future native
branch, fetched packet or simulation relation. -/
@[expose] def Halted (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  ((g.rules rule).symbol=(g.tape node).symbol ∧ (g.rules rule).destination=none) ∨
  ((g.rules rule).symbol≠(g.tape node).symbol ∧
    ((g.rules rule).scanNext≠true ∨ g.transitions≤rule.val+1))
@[expose] def initial (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FullTableReset.initial mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory) seed
@[expose] def program (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FullTableReset.program mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory) seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FullTableReset.finish mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory) seed

theorem chosen_iff (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol=true ↔
      (g.rules rule).symbol=(g.tape node).symbol := by
  change Listing8InputComposition.chosen (g.rules rule).symbol (g.tape node).symbol=true ↔ _
  exact Listing8InputComposition.chosen_iff _ _
theorem halt_condition (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (halted : Halted g node rule) :
    (if Listing8LiteralInput.chosen (values mode origin g node rule).rule (values mode origin g node rule).tape
      then (values mode origin g node rule).newState else (values mode origin g node rule).next)=
      Arithmetic.encodeNat mode (nodePC mode origin g g.halt) := by
  rcases halted with ⟨same,destination⟩ | ⟨different,scan⟩
  · have chosen:=(chosen_iff g node rule).mpr same
    simp only [values,chosen,ite_true,destination,statePC]
  · have chosen : Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol=false := by
      cases found : Listing8LiteralInput.chosen (g.rules rule).symbol (g.tape node).symbol
      · rfl
      · exact False.elim (different ((chosen_iff g node rule).mp found))
    have stop : ¬((g.rules rule).scanNext=true ∧ rule.val+1<g.transitions) := by
      intro follow
      rcases scan with no | last
      · exact no follow.1
      · omega
    simp only [values,chosen,reduceCtorEq,ite_false,nextPC,stop]

/-- Actual body/failure/table/reset/DOHALT execution on the constructed source
graph. Original declaration and reset bounds are derived; body/copy placement
conditions remain explicit. The endpoint is the start of the input declarations. -/
theorem run (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (nodeLocated : l.sourceNode=nodePC mode origin g node) (ruleLocated : l.sourceTransition=rulePC mode origin g rule)
    (r : Listing8CopyImage.Resources mode l) (fields : Listing8GraphOwnerBounds.Fields mode l)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8GraphPointers.Bounds mode origin g) (halted : Halted g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (initial mode origin l t g node rule memory seed) (program mode origin l t g node rule memory seed)
      (finish mode origin l t g node rule memory seed) ∧
    (finish mode origin l t g node rule memory seed).principal.pc.toNat=Listing8GraphLayout.input mode origin g.transitions ∧
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g g.halt) ∧
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) ∧
    (finish mode origin l t g node rule memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule memory seed).backwards=false := by
  have owners:=Listing8GraphOwnerBounds.bounds mode origin l g node rule boot.packed fields bounds
  have actual:=Listing8FullTableRun.run mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (table mode origin g) rule.val (selected mode origin g node rule) ruleLocated r owners copies boot body
    (Listing8GraphTableBounds.reset_bounds mode origin g node l t _ nodeLocated boot body bounds)
    (halt_condition mode origin g node rule halted) (Listing8GraphNodeImage.image mode origin g memory) seed
  have endpoint : origin+(if mode=.x86 then 901 else 1399)+(table mode origin g).length*Listing8Prototypes.transitionSpan mode=
      Listing8GraphLayout.input mode origin g.transitions := by
    rw [table_length]
    dsimp [Listing8GraphLayout.input,Listing8GraphLayout.reset,Listing8GraphLayout.transition,Listing8FullTableImage.start]
    rw [Listing8FailLayout.end_offset]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
  rw [endpoint] at actual
  exact actual
end SmcTuring.Appendix.Listing8GraphRun

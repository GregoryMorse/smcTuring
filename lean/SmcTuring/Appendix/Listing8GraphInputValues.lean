module
public import SmcTuring.Appendix.Listing8GraphInputRun

public section
namespace SmcTuring.Appendix.Listing8GraphInputValues
open Native Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphBodyNodes Listing8GraphInputRun

/-- Complete indexed tape output and both graph neighbors are retained
through all original input declarations, not just the selected tape node. -/
theorem fields (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (query : Fin g.nodes) :
    DwordCode.get (finish mode origin l t g node rule memory seed).principal.memory (nodePC mode origin g query+6)=symbol g node rule query ∧
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory
      (pointerField mode (backEntry mode (nodePC mode origin g query)))=Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).back) ∧
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory
      (pointerField mode (forwardEntry mode (nodePC mode origin g query)))=Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).forward) := by
  rw [(result mode origin l t g node rule ctx memory seed).2.1]
  exact Listing8GraphResetNodes.fields mode origin l t g node rule ctx memory seed query

theorem cursors (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (halted : Listing8GraphRun.Halted g node rule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g g.halt) ∧
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) := by
  rw [(result mode origin l t g node rule ctx memory seed).2.1]
  have actual:=Listing8GraphRun.run mode origin l t g node rule ctx.nodeLocated ctx.ruleLocated ctx.resources ctx.fields
    ctx.copies ctx.boot ctx.body ctx.native halted memory seed
  exact ⟨actual.2.2.1,actual.2.2.2.1⟩

theorem registers (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (halted : Listing8GraphRun.Halted g node rule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule memory seed).backwards=false := by
  have frames:=result mode origin l t g node rule ctx memory seed
  have actual:=Listing8GraphRun.run mode origin l t g node rule ctx.nodeLocated ctx.ruleLocated ctx.resources ctx.fields
    ctx.copies ctx.boot ctx.body ctx.native halted memory seed
  exact ⟨frames.2.2.1.trans actual.2.2.2.2.1,frames.2.2.2.1.trans actual.2.2.2.2.2.1,
    frames.2.2.2.2.1.trans actual.2.2.2.2.2.2.1,frames.2.2.2.2.2.1.trans actual.2.2.2.2.2.2.2.1,
    frames.2.2.2.2.2.2.trans actual.2.2.2.2.2.2.2.2⟩

theorem endpoint_offset (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc.toNat=
      origin+(if mode=.x86 then 901 else 1399)+g.transitions*transitionSpan mode+g.nodes*nodeSpan mode := by
  rw [endpoint mode origin l t g node rule ctx memory seed]
  dsimp [Listing8GraphLayout.endPC,Listing8GraphLayout.node,Listing8GraphLayout.input,
    Listing8GraphLayout.reset,Listing8GraphLayout.transition,Listing8FullTableImage.start]
  rw [Listing8FailLayout.end_offset]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

/-- One actual continuous trace through the complete printed input tail,
with all indexed output, exact endpoint, reset cursors and register frames. -/
theorem run (mode : Mode) (origin : Nat) (l : Listing8CopyImage.Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (halted : Listing8GraphRun.Halted g node rule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphRun.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) ∧
    (finish mode origin l t g node rule memory seed).principal.pc.toNat=
      origin+(if mode=.x86 then 901 else 1399)+g.transitions*transitionSpan mode+g.nodes*nodeSpan mode ∧
    (∀ query : Fin g.nodes,DwordCode.get (finish mode origin l t g node rule memory seed).principal.memory
      (nodePC mode origin g query+6)=symbol g node rule query ∧
      MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory
        (pointerField mode (backEntry mode (nodePC mode origin g query)))=Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).back) ∧
      MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory
        (pointerField mode (forwardEntry mode (nodePC mode origin g query)))=Arithmetic.encodeNat mode (nodePC mode origin g (g.tape query).forward)) ∧
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode (nodePC mode origin g g.halt) ∧
    MixedMemory.getWord mode (finish mode origin l t g node rule memory seed).principal.memory (Listing8StateGeometry.region mode l).cursor=
      Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) ∧
    (finish mode origin l t g node rule memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule memory seed).principal.carry=false ∧
    (finish mode origin l t g node rule memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule memory seed).backwards=false :=
  ⟨trace mode origin l t g node rule ctx halted memory seed,endpoint_offset mode origin l t g node rule ctx memory seed,
    fields mode origin l t g node rule ctx memory seed,(cursors mode origin l t g node rule ctx halted memory seed).1,
    (cursors mode origin l t g node rule ctx halted memory seed).2,registers mode origin l t g node rule ctx halted memory seed⟩
end SmcTuring.Appendix.Listing8GraphInputValues

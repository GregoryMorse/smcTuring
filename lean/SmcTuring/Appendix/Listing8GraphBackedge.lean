module
public import SmcTuring.Appendix.Listing8GraphLabels
public import SmcTuring.Appendix.Listing8BeginReturn

public section
namespace SmcTuring.Appendix.Listing8GraphBackedge
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def backing (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8FailImage.backing mode origin (Listing8FullTableImage.backing mode origin (table mode origin g)
    (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g)
      (Listing8GraphNodeImage.image mode origin g memory)))
@[expose] def initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalJump.initial mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (backing mode origin l g memory) seed
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8BeginReturn.program mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (backing mode origin l g memory) seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8BeginReturn.finish mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (backing mode origin l g memory) seed
@[expose] def failed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalJump.failed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (backing mode origin l g memory) seed

theorem failed_iff (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    failed mode origin l t g node rule memory seed=true ↔ Listing8GraphRun.Halted g node rule := by
  rw [failed,Listing8JumpValues.failure_condition mode origin l t _ _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body]
  simp only [decide_eq_true_eq]
  exact Listing8GraphLabels.native_halt_iff mode origin g node rule ctx.native
theorem nonfailure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    failed mode origin l t g node rule memory seed=false := by
  cases result : failed mode origin l t g node rule memory seed
  · rfl
  · exact False.elim (nonhalt ((failed_iff mode origin l t g node rule ctx memory seed).mp result))
/-- The branch is derived from the initial graph. All actual current-byte
body, CALL and begin instructions form one trace with no next-pass image. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) :=
  Listing8BeginReturn.trace mode origin l t _ _ ctx.resources (owners mode origin l t g node rule ctx)
    ctx.copies ctx.boot ctx.body _ seed (nonfailure mode origin l t g node rule ctx memory seed nonhalt)
theorem effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    finish mode origin l t g node rule memory seed=
      {bodyEnd mode origin l t g node rule memory seed with principal:={
        (bodyEnd mode origin l t g node rule memory seed).principal with pc:=Arithmetic.encodeNat mode l.start,carry:=false}} :=
  Listing8BeginReturn.effect mode origin l t _ _ ctx.resources (owners mode origin l t g node rule ctx)
    ctx.copies ctx.boot ctx.body _ seed
theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=(if mode=.x86 then 147 else 195) :=
  Listing8BeginReturn.instruction_count mode origin l t _ _ _ seed
theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode l.start ∧
    (finish mode origin l t g node rule memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t g node rule memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t g node rule memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t g node rule memory seed).backwards=false ∧
    (finish mode origin l t g node rule memory seed).principal.carry=false := by
  have prior:=Listing8GlobalBootValues.registers mode origin l t (values mode origin g node rule) _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body
    (Listing8JumpImage.backing mode origin (backing mode origin l g memory)) seed
  change (bodyEnd mode origin l t g node rule memory seed).principal.stack=seed.principal.stack ∧ _ at prior
  rw [effect mode origin l t g node rule ctx memory seed]
  exact ⟨rfl,prior.1,prior.2.1,prior.2.2.1,prior.2.2.2.1,rfl⟩

end SmcTuring.Appendix.Listing8GraphBackedge

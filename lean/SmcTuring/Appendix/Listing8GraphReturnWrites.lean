module
public import SmcTuring.Appendix.Listing8GraphEntryWrites

public section
namespace SmcTuring.Appendix.Listing8GraphReturnWrites
set_option maxHeartbeats 1000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphJumpWrites.program mode origin l t g node rule memory seed++
    Listing4TargetLayout.forms mode origin (Listing8BootImage.beginPC mode origin)

theorem jump_state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed=
      Listing8GlobalJump.finish mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8GraphBackedge.backing mode origin l g memory) seed := by
  unfold Listing8GraphJumpWrites.finish Listing8GlobalJump.finish
  rw [Listing8GraphJumpWrites.failure_state mode origin l t g node rule ctx memory seed]
  rfl

theorem return_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing4TargetLayout.forms mode origin (Listing8BootImage.beginPC mode origin))
      (Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed) := by
  have capacity:=Listing8GlobalBoot.entry_capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  have notFailed : Listing8GlobalJump.failed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8GraphBackedge.backing mode origin l g memory) seed=false :=
    Listing8GraphBackedge.nonfailure mode origin l t g node rule ctx memory seed nonhalt
  have shape:=Listing8BeginReturn.call_shape mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (Listing8GraphBackedge.backing mode origin l g memory) seed
  simp only [Listing8BeginReturn.target,notFailed,Bool.false_eq_true,ite_false] at shape
  rw [jump_state mode origin l t g node rule ctx memory seed,shape]
  exact Listing4TargetWrites.owned mode origin _ origin (Listing8BootImage.beginPC mode origin)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin))
    (Listing8BeginReturn.targetSeed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8GraphBackedge.backing mode origin l g memory) seed)
    (Listing4EntryLayout.begin_ranges mode origin) (Listing4EntryLayout.stack_capacity mode origin capacity)
    ⟨Nat.le_refl _,Listing8GraphJumpWrites.stack_inside mode origin l t g node rule ctx⟩
    (Listing8StackMetadata.stack_packet mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed)

theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  unfold program
  exact StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed)
    (Listing4TargetLayout.forms mode origin (Listing8BootImage.beginPC mode origin))
    (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) (Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed)
    (Listing8GraphJumpWrites.trace mode origin l t g node rule ctx memory seed)
    (Listing8GraphEntryWrites.owned mode origin l t g node rule ctx memory seed) (return_owned mode origin l t g node rule ctx memory seed nonhalt)

/-- The computed nonhalt branch executes the original bootstrap, complete
first body/CALL and actual five-instruction begin return from one image. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) := by
  have capacity:=Listing8GlobalBoot.entry_capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  have notFailed : Listing8GlobalJump.failed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8GraphBackedge.backing mode origin l g memory) seed=false :=
    Listing8GraphBackedge.nonfailure mode origin l t g node rule ctx memory seed nonhalt
  have shape:=Listing8BeginReturn.call_shape mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (Listing8GraphBackedge.backing mode origin l g memory) seed
  simp only [Listing8BeginReturn.target,notFailed,Bool.false_eq_true,ite_false] at shape
  have last:=Listing4TargetTrace.trace mode origin (Listing8BootImage.beginPC mode origin)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin))
    (Listing8BeginReturn.targetSeed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8GraphBackedge.backing mode origin l g memory) seed)
    (Listing4EntryLayout.begin_ranges mode origin) (Listing4EntryLayout.stack_capacity mode origin capacity)
    (Listing4EntryLayout.target_capacity mode origin capacity)
    (Listing8StackMetadata.stack_packet mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed)
    (Listing4EntryLayout.target_after_stack mode origin)
    (Listing8BeginReturn.target_current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (Listing8GraphBackedge.backing mode origin l g memory) seed)
  rw [←shape,←jump_state mode origin l t g node rule ctx memory seed] at last
  exact StringStack.trace_append mode (Listing8GraphJumpWrites.trace mode origin l t g node rule ctx memory seed) last

/-- All 147/195 instructions, including bootstrap and first begin return,
have complete nonempty architectural stores inside emitted code. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  ⟨trace mode origin l t g node rule ctx memory seed nonhalt,owned mode origin l t g node rule ctx memory seed nonhalt⟩

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=if mode=.x86 then 147 else 195 := by
  rw [program,List.length_append,Listing8GraphJumpWrites.instruction_count,Listing4TargetLayout.instruction_count]
  cases mode <;> rfl

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode l.start ∧
    (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.stack=seed.principal.stack ∧
    (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).sourceIndex=seed.sourceIndex ∧
    (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).destinationIndex=seed.destinationIndex ∧
    (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).backwards=false ∧
    (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.carry=false :=
  Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed

end SmcTuring.Appendix.Listing8GraphReturnWrites

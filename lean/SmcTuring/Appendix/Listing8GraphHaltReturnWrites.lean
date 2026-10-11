module
public import SmcTuring.Appendix.Listing8GraphReturnWrites
public import SmcTuring.Appendix.Listing8GraphNextFailImage

public section
namespace SmcTuring.Appendix.Listing8GraphHaltReturnWrites
set_option maxHeartbeats 1000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def backing (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8FullTableImage.backing mode origin (table mode origin g)
    (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory))
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailReturn.finish mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (backing mode origin l g memory) seed
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphJumpWrites.program mode origin l t g node rule memory seed++Listing4TargetLayout.forms mode origin (Listing8JumpLayout.failPC mode origin)

theorem call_shape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed=
      Listing4TargetEffects.entry mode origin (Listing8JumpLayout.failPC mode origin)
        (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin))
        (Listing8BeginReturn.targetSeed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
          (Listing8GraphBackedge.backing mode origin l g memory) seed) := by
  have failed : Listing8GlobalJump.failed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8GraphBackedge.backing mode origin l g memory) seed=true :=
    (Listing8GraphBackedge.failed_iff mode origin l t g node rule ctx memory seed).mpr halted
  have shape:=Listing8BeginReturn.call_shape mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (Listing8GraphBackedge.backing mode origin l g memory) seed
  rw [Listing8GraphReturnWrites.jump_state mode origin l t g node rule ctx memory seed]
  simpa only [Listing8BeginReturn.target,failed,ite_true] using shape

theorem return_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing4TargetLayout.forms mode origin (Listing8JumpLayout.failPC mode origin)) (Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed) := by
  rw [call_shape mode origin l t g node rule ctx memory seed halted]
  exact Listing4TargetWrites.owned mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) origin (Listing8JumpLayout.failPC mode origin)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin))
    (Listing8BeginReturn.targetSeed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8GraphBackedge.backing mode origin l g memory) seed)
    (Listing8FailLayout.ranges mode origin) (Listing8JumpLayout.stack_capacity mode origin
      (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body))
    ⟨Nat.le_refl _,Listing8GraphJumpWrites.stack_inside mode origin l t g node rule ctx⟩
    (Listing8StackMetadata.stack_packet mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed)

theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  unfold program
  exact StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed) (Listing4TargetLayout.forms mode origin (Listing8JumpLayout.failPC mode origin))
    (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) (Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed)
    (Listing8GraphJumpWrites.trace mode origin l t g node rule ctx memory seed)
    (Listing8GraphEntryWrites.owned mode origin l t g node rule ctx memory seed) (return_owned mode origin l t g node rule ctx memory seed halted)

theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) := by
  have last:=Listing4TargetTrace.trace mode origin (Listing8JumpLayout.failPC mode origin)
    (Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin))
    (Listing8BeginReturn.targetSeed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8GraphBackedge.backing mode origin l g memory) seed)
    (Listing8FailLayout.ranges mode origin) (Listing8JumpLayout.stack_capacity mode origin
      (Listing8JumpImage.capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body))
    (Listing8FailLayout.capacity mode origin l (Listing8FullTableImage.start mode origin) (Listing8GraphNextFailImage.tail_bounds mode origin l t g node rule ctx))
    (Listing8StackMetadata.stack_packet mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed)
    (Listing8FailLayout.placement mode origin)
    (Listing8FailImage.current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8FullTableImage.start mode origin)
      ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8GraphNextFailImage.tail_bounds mode origin l t g node rule ctx) (backing mode origin l g memory) seed)
  rw [←call_shape mode origin l t g node rule ctx memory seed halted] at last
  exact StringStack.trace_append mode (Listing8GraphJumpWrites.trace mode origin l t g node rule ctx memory seed) last

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=if mode=.x86 then 147 else 195 := by
  rw [program,List.length_append,Listing8GraphJumpWrites.instruction_count,Listing4TargetLayout.instruction_count]
  cases mode <;> rfl

end SmcTuring.Appendix.Listing8GraphHaltReturnWrites

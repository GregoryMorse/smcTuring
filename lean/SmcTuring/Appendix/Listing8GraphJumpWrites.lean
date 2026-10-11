module
public import SmcTuring.Appendix.Listing8GraphFailureWrites
public import SmcTuring.Appendix.Listing8JumpWrites

public section
namespace SmcTuring.Appendix.Listing8GraphJumpWrites
set_option maxHeartbeats 1000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def forms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphFailureWrites.forms mode origin l t g node rule memory seed++
    Listing8JumpLayout.forms mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing4EntryLayout.forms mode origin++forms mode origin l t g node rule memory seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8JumpEffects.finish mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed)
    (Listing8GraphFailureWrites.finish mode origin l t g node rule memory seed)

theorem stack_inside (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    origin+Listing4StackLayout.size mode≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  have upper:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
    (Listing8LoopTailGeometry.input_before_end mode origin g)
  change Listing8FailureLayout.callPC mode (Listing8BootControl.region mode origin l (nodePC mode origin g g.halt))+5≤_ at upper
  rw [Listing8JumpImage.call_position mode origin l t _ ctx.boot ctx.body] at upper
  cases mode <;> dsimp [Listing4StackLayout.size,Listing8JumpLayout.callPC,Listing8JumpLayout.jumpPC,Listing4JumpLayout.prefixSize] at upper ⊢ <;> omega

theorem failure_state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphFailureWrites.finish mode origin l t g node rule memory seed=
      Listing8GlobalJump.bodyEnd mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8GraphBackedge.backing mode origin l g memory) seed := by
  unfold Listing8GraphFailureWrites.finish Listing8GlobalJump.bodyEnd Listing8GlobalBoot.finish Listing8GlobalFailure.finish
  rw [Listing8GraphFailureWrites.state_state mode origin l t g node rule ctx memory seed]
  rfl

theorem failure_run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.run mode (Listing8GraphFailureWrites.forms mode origin l t g node rule memory seed)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)=
        Listing8GraphFailureWrites.finish mode origin l t g node rule memory seed := by
  have actual:=StringWrites.trace_run_eq mode (Listing8GraphFailureWrites.execute mode origin l t g node rule ctx memory seed).1
  have bootRun:=StringWrites.trace_run_eq mode (Listing4Entry.trace mode origin
    (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))
  change StringWrites.run mode (Listing4EntryLayout.forms mode origin)
    (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)=Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed at bootRun
  rw [Listing8GraphFailureWrites.program,StringWrites.run_append,bootRun] at actual
  exact actual

theorem jump_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8JumpLayout.forms mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed))
      (Listing8GraphFailureWrites.finish mode origin l t g node rule memory seed) := by
  rw [failure_state mode origin l t g node rule ctx memory seed]
  exact Listing8JumpWrites.owned mode origin _ origin _ _
    (Listing8GlobalBoot.endpoint mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed)
    (Listing8JumpImage.capacity mode origin l t _ ctx.boot ctx.body)
    ⟨Nat.le_refl _,stack_inside mode origin l t g node rule ctx⟩
    (Listing8StackMetadata.stack_packet mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed)

theorem body_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  rw [forms,StringWrites.owned_run_append,failure_run mode origin l t g node rule ctx memory seed]
  exact ⟨Listing8GraphFailureWrites.body_owned mode origin l t g node rule ctx memory seed,
    jump_owned mode origin l t g node rule ctx memory seed⟩

/-- One original graph initialization executes the complete first body and CALL.
Every 134/177 reached body instruction has a complete code-owned store. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) := by
  have last:=Listing8JumpTrace.trace mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed)
    (Listing8GlobalJump.bodyEnd mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8GraphBackedge.backing mode origin l g memory) seed)
    (Listing8GlobalBoot.endpoint mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed)
    (Listing8JumpImage.capacity mode origin l t _ ctx.boot ctx.body)
    (Listing8StackMetadata.stack_packet mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed)
    (Listing8JumpImage.current mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8GraphBackedge.backing mode origin l g memory) seed)
    (Listing8GlobalJump.call_packet mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body
      (Listing8GraphBackedge.backing mode origin l g memory) seed)
  rw [←failure_state mode origin l t g node rule ctx memory seed] at last
  have first:=(Listing8GraphFailureWrites.execute mode origin l t g node rule ctx memory seed).1
  unfold program forms
  rw [←List.append_assoc]
  exact StringStack.trace_append mode first last

set_option maxHeartbeats 2000000 in
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  constructor
  · exact trace mode origin l t g node rule ctx memory seed
  · exact body_owned mode origin l t g node rule ctx memory seed

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=if mode=.x86 then 142 else 190 := by
  have prior:=Listing8GraphFailureWrites.instruction_count mode origin l t g node rule memory seed
  rw [Listing8GraphFailureWrites.program,List.length_append] at prior
  rw [program,List.length_append,forms,List.length_append,Listing8JumpLayout.instruction_count]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at prior ⊢ <;> omega

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc=
      if Listing8GraphBackedge.failed mode origin l t g node rule memory seed then Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin)
        else Arithmetic.encodeNat mode (Listing8BootImage.beginPC mode origin) := by
  unfold finish
  rw [failure_state mode origin l t g node rule ctx memory seed]
  have actual:=Listing8GlobalJump.effect mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (Listing8GraphBackedge.backing mode origin l g memory) seed
  change Listing8JumpEffects.finish mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed) _=_ at actual
  rw [actual]
  rfl

end SmcTuring.Appendix.Listing8GraphJumpWrites

module
public import SmcTuring.Appendix.Listing8GraphBodySequential

public section
namespace SmcTuring.Appendix.Listing8GraphBodyFetch
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringPCWindows.Run StringFetchWindows.Run

theorem short (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing8GraphFailureWrites.program mode origin l t g node rule memory seed).length*15<2^(8*mode.wordBytes) := by
  rw [Listing8GraphFailureWrites.instruction_count]
  cases mode <;> decide

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing8GraphFailureWrites.finish mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin) := by
  rw [Listing8GraphFailureWrites.endpoint mode origin l t g node rule ctx memory seed]
  have position:=Listing8JumpImage.end_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.endPC mode (Listing8GraphFailureWrites.region mode origin l g)=Listing8JumpLayout.jumpPC mode origin at position
  rw [position]

theorem windows (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringPCWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphFailureWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  apply StringPCMargins.of_trace mode _ (Listing8GraphFailureWrites.execute mode origin l t g node rule ctx memory seed).1
    origin (Listing8JumpLayout.jumpPC mode origin) (Listing8GraphBodySequential.sequential mode origin l t g node rule memory seed)
    rfl (endpoint mode origin l t g node rule ctx memory seed) ?_
    (short mode origin l t g node rule memory seed) (Nat.le_refl _) (Listing8BodyFetch.margin mode origin g.transitions g.nodes) ctx.native.capacity
  cases mode <;> dsimp [Listing8JumpLayout.jumpPC] <;> omega

theorem byte_total (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringPCSteps.total mode (Listing8GraphFailureWrites.program mode origin l t g node rule memory seed)=(if mode=.x86 then 795 else 1247) := by
  have actual:=(Listing8GraphFailureWrites.execute mode origin l t g node rule ctx memory seed).1
  have margin:=Listing8BodyFetch.margin mode origin g.transitions g.nodes
  have capacity:=ctx.native.capacity
  have ordered : origin≤Listing8JumpLayout.jumpPC mode origin := by cases mode <;> dsimp [Listing8JumpLayout.jumpPC] <;> omega
  have span:=StringPCMargins.endpoint_span mode actual origin (Listing8JumpLayout.jumpPC mode origin)
    (Listing8GraphBodySequential.sequential mode origin l t g node rule memory seed) rfl
    (endpoint mode origin l t g node rule ctx memory seed) ordered (by omega)
    (Nat.lt_of_le_of_lt (StringInstructionSizes.trace_total mode actual) (short mode origin l t g node rule memory seed))
  cases mode <;> simp [Listing8JumpLayout.jumpPC] at span ⊢ <;> omega

theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphFailureWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  StringFetchWindows.of_pc_run mode _ (Listing8GraphFailureWrites.execute mode origin l t g node rule ctx memory seed).1
    (windows mode origin l t g node rule ctx memory seed)

end SmcTuring.Appendix.Listing8GraphBodyFetch

module
public import SmcTuring.Appendix.Listing8GraphEntryFetch
public import SmcTuring.Appendix.Listing8GraphReturnReads

public section
namespace SmcTuring.Appendix.Listing8GraphReturnFetch
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringPCWindows.Run StringFetchWindows.Run

theorem target_windows (mode : Mode) (origin transitions nodes : Nat) (failed : Bool)
    (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpReturn.target mode origin failed))
    (capacity : Listing8GraphLayout.endPC mode origin transitions nodes<2^(8*mode.wordBytes)) :
    StringPCWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin transitions nodes⟩
      (Listing4TargetLayout.forms mode origin (Listing8JumpReturn.target mode origin failed)) state := by
  have placed:=Listing8LoopReturnFetch.placement mode origin transitions nodes failed
  apply StringPCWindows.sequential mode _ _ state _
    (Listing8JumpPCWindows.target_sequential mode origin _) entry (Listing8JumpPCWindows.target_guard mode origin _)
    placed.target.1 ?_ capacity
  rw [Listing8JumpPCWindows.target_total]
  exact placed.target.2

theorem backedge_windows (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    StringPCWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphReturnWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  have notFailed : Listing8GlobalJump.failed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8GraphBackedge.backing mode origin l g memory) seed=false :=
    Listing8GraphBackedge.nonfailure mode origin l t g node rule ctx memory seed nonhalt
  have shape:=Listing8BeginReturn.call_shape mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.boot ctx.body (Listing8GraphBackedge.backing mode origin l g memory) seed
  have position : (Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8BootImage.beginPC mode origin) := by
    rw [Listing8GraphReturnWrites.jump_state mode origin l t g node rule ctx memory seed,shape]
    change Arithmetic.encodeNat mode (Listing8BeginReturn.target mode origin l t (values mode origin g node rule)
      (nodePC mode origin g g.halt) (Listing8GraphBackedge.backing mode origin l g memory) seed)=_
    simp only [Listing8BeginReturn.target,notFailed,Bool.false_eq_true,ite_false]
  unfold Listing8GraphReturnWrites.program
  exact StringPCWindows.append_trace mode _ _ _ _ (Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed)
    (Listing8GraphJumpWrites.trace mode origin l t g node rule ctx memory seed)
    (Listing8GraphEntryFetch.windows mode origin l t g node rule ctx memory seed)
    (target_windows mode origin g.transitions g.nodes false _ position ctx.native.capacity)

theorem halt_windows (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringPCWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphHaltReturnWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  have position : (Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8JumpLayout.failPC mode origin) := by
    rw [Listing8GraphHaltReturnWrites.call_shape mode origin l t g node rule ctx memory seed halted]
    rfl
  unfold Listing8GraphHaltReturnWrites.program
  exact StringPCWindows.append_trace mode _ _ _ _ (Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed)
    (Listing8GraphJumpWrites.trace mode origin l t g node rule ctx memory seed)
    (Listing8GraphEntryFetch.windows mode origin l t g node rule ctx memory seed)
    (target_windows mode origin g.transitions g.nodes true _ position ctx.native.capacity)

theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphReturnWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  StringFetchWindows.of_pc_run mode _ (Listing8GraphReturnWrites.trace mode origin l t g node rule ctx memory seed nonhalt)
    (backedge_windows mode origin l t g node rule ctx memory seed nonhalt)

theorem halted (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (halted : Listing8GraphRun.Halted g node rule) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphHaltReturnWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  StringFetchWindows.of_pc_run mode _ (Listing8GraphHaltReturnWrites.trace mode origin l t g node rule ctx memory seed halted)
    (halt_windows mode origin l t g node rule ctx memory seed halted)

end SmcTuring.Appendix.Listing8GraphReturnFetch

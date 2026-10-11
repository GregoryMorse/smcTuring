module
public import SmcTuring.Appendix.Listing8BodySequential
public import SmcTuring.Appendix.Listing8LoopReturnFetch
public import SmcTuring.Appendix.Listing8LoopReads
public import SmcTuring.Native.StringPCMargins

public section
namespace SmcTuring.Appendix.Listing8BodyFetch
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Current:=Listing8LoopGraphFailure.Current
attribute [local irreducible] StringPCWindows.Run StringFetchWindows.Run StringWrites.OwnedRun StringReadRuns.Run

abbrev forms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :=
  (Listing8LoopFailure.program mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin) state).map StringStack.Form.previous

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    (Listing8LoopControl.failureEnd mode origin l t g node rule state).principal.pc=
      Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin) := by
  have bounds:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current
  rw [Listing8LoopControl.failureEnd,Listing8LoopFailure.endpoint mode l t (values mode origin g node rule)
    (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old bounds state current.state.head.graph.entry current.state.head.graph.forward image]
  have position:=Listing8JumpImage.end_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.endPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.jumpPC mode origin at position
  rw [position]

theorem short (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (state : StringExecution.State mode) :
    (forms mode origin l t g node rule state).length*15<2^(8*mode.wordBytes) := by
  rw [forms,List.length_map,Listing8LoopFailure.instruction_count]
  cases mode <;> decide

theorem ordered (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    origin≤l.start ∧ l.start≤Listing8JumpLayout.jumpPC mode origin := by
  rw [ctx.boot.packed]
  cases mode <;> dsimp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size,Listing8JumpLayout.jumpPC] <;> omega

/-- Original graph geometry reserves the classifier header beyond the
positively proved body endpoint, including short MOVS instructions. -/
theorem margin (mode : Mode) (origin transitions nodes : Nat) :
    Listing8JumpLayout.jumpPC mode origin+3≤Listing8GraphLayout.endPC mode origin transitions nodes := by
  have placed:=Listing8LoopReturnFetch.placement mode origin transitions nodes true
  have upper:=placed.jump.2
  dsimp [Listing8JumpLayout.failPC,Listing8JumpLayout.callPC] at upper
  omega

theorem pc_windows (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringPCWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (forms mode origin l t g node rule state) state := by
  have actual:=(Listing8LoopFailureWrites.execute mode origin l t g node rule ctx old state current).1
  have positions:=ordered mode origin l t g node rule ctx
  exact StringPCMargins.of_trace mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ actual
    l.start (Listing8JumpLayout.jumpPC mode origin)
    (Listing8BodySequential.failure mode l t _ _ _ state) current.state.head.graph.entry
    (endpoint mode origin l t g node rule ctx old state current) positions.2
    (short mode origin l t g node rule state) positions.1 (margin mode origin g.transitions g.nodes) ctx.native.capacity

/-- Exact original 743/1150-byte body span follows the actual endpoint,
sequential forms and small decoded instruction total; no wrap is assumed. -/
theorem byte_total (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringPCSteps.total mode (forms mode origin l t g node rule state)=(if mode=.x86 then 743 else 1150) := by
  have actual:=(Listing8LoopFailureWrites.execute mode origin l t g node rule ctx old state current).1
  have ending:=margin mode origin g.transitions g.nodes
  have capacity:=ctx.native.capacity
  have span:=StringPCMargins.endpoint_span mode actual l.start (Listing8JumpLayout.jumpPC mode origin)
    (Listing8BodySequential.failure mode l t _ _ _ state) current.state.head.graph.entry
    (endpoint mode origin l t g node rule ctx old state current) (ordered mode origin l t g node rule ctx).2
    (by omega) (Nat.lt_of_le_of_lt (StringInstructionSizes.trace_total mode actual) (short mode origin l t g node rule state))
  rw [ctx.boot.packed] at span
  unfold forms
  cases mode <;> simp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size,Listing8JumpLayout.jumpPC] at span ⊢ <;> omega

theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (forms mode origin l t g node rule state) state :=
  StringFetchWindows.of_pc_run mode _ (Listing8LoopFailureWrites.execute mode origin l t g node rule ctx old state current).1
    (pc_windows mode origin l t g node rule ctx old state current)

/-- The complete actual pre-CALL body retains one trace with every fetch,
data-read and complete store certified from the same initial invariant. -/
theorem complete (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state (forms mode origin l t g node rule state) (Listing8LoopControl.failureEnd mode origin l t g node rule state) ∧
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ (forms mode origin l t g node rule state) state ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) (forms mode origin l t g node rule state) state ∧
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ (forms mode origin l t g node rule state) state := by
  have actual:=Listing8LoopFailureWrites.execute mode origin l t g node rule ctx old state current
  exact ⟨actual.1,contained mode origin l t g node rule ctx old state current,actual.2,
    Listing8LoopReads.failure mode origin l t g node rule ctx old state current⟩

end SmcTuring.Appendix.Listing8BodyFetch

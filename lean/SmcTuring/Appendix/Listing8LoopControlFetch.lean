module
public import SmcTuring.Appendix.Listing8BodyFetch

public section
namespace SmcTuring.Appendix.Listing8LoopControlFetch
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
abbrev Current:=Listing8LoopControl.Current
attribute [local irreducible] StringFetchWindows.Run StringWrites.OwnedRun StringReadRuns.Run

/-- Every actual request in one complete 139/182-instruction body follows
the maintained present entry and original geometry, including both CALL
outcomes. No later PC, window, readiness, packet or trace is supplied. -/
theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8LoopControl.program mode origin l t g node rule state) state := by
  have body:=Listing8BodyFetch.complete mode origin l t g node rule ctx old state current.body
  rw [Listing8LoopControl.program]
  exact StringFetchWindows.append_trace mode _ _ _ state (Listing8LoopControl.failureEnd mode origin l t g node rule state)
    body.1 body.2.1 (Listing8LoopReturnFetch.contained mode origin l t g node rule ctx old state current)

theorem complete (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    StringStack.Trace mode state (Listing8LoopControl.program mode origin l t g node rule state) (Listing8LoopControl.finish mode origin l t g node rule state) ∧
    StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ (Listing8LoopControl.program mode origin l t g node rule state) state ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) (Listing8LoopControl.program mode origin l t g node rule state) state ∧
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ (Listing8LoopControl.program mode origin l t g node rule state) state ∧
    (Listing8LoopControl.program mode origin l t g node rule state).length=(if mode=.x86 then 139 else 182) ∧
    (Listing8LoopControl.finish mode origin l t g node rule state).principal.stack=state.principal.stack ∧
    (Listing8LoopControl.finish mode origin l t g node rule state).sourceIndex=state.sourceIndex ∧
    (Listing8LoopControl.finish mode origin l t g node rule state).destinationIndex=state.destinationIndex ∧
    (Listing8LoopControl.finish mode origin l t g node rule state).backwards=false ∧
    (Listing8LoopControl.finish mode origin l t g node rule state).principal.carry=false ∧
    (Listing8LoopControl.finish mode origin l t g node rule state).principal.accumulator=
      (Listing8LoopControl.failureEnd mode origin l t g node rule state).principal.accumulator := by
  have actual:=Listing8LoopControlWrites.execute mode origin l t g node rule ctx old state current
  exact ⟨actual.1,contained mode origin l t g node rule ctx old state current,actual.2,
    Listing8LoopReads.control mode origin l t g node rule ctx old state current,
    Listing8LoopControl.instruction_count mode origin l t g node rule state,
    Listing8LoopControl.registers mode origin l t g node rule ctx old state current⟩

theorem next_access (mode : Mode) (environment : MappedExecution.Environment) (origin : Nat)
    (l : Layout) (t : Targets) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (mapping : MappedExecution.Mapped mode environment ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩)
    (ctx : Context mode origin l t g node rule) (old : OldInput) (state : StringExecution.State mode)
    (current : Current mode origin l t g node rule old state)
    (before : List (StringStack.Form mode)) (form : StringStack.Form mode) (after : List (StringStack.Form mode))
    (cut : before++form::after=Listing8LoopControl.program mode origin l t g node rule state) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      StringFetchWindows.Within mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ reached ∧
      StringFetchPermissions.Allowed mode environment reached ∧
      StringWrites.CodeWrite mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) form reached ∧
      MappedExecution.Window mode environment .write (StringWrites.packet mode form reached).address (StringWrites.packet mode form reached).bytes.length ∧
      StringReadWindows.Within mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ form reached ∧
      StringReadPermissions.Allowed mode environment form reached ∧
      StringStack.Trace mode (StringStack.execute mode form reached) after (Listing8LoopControl.finish mode origin l t g node rule state) := by
  have facts:=complete mode origin l t g node rule ctx old state current
  exact StringFetchPermissions.next_access mode environment origin _ mapping facts.1 facts.2.1 facts.2.2.1 facts.2.2.2.1 before form after cut

end SmcTuring.Appendix.Listing8LoopControlFetch

module
public import SmcTuring.Appendix.Listing8LoopTerminal
public import SmcTuring.Appendix.Listing8LoopIterationReads
public import SmcTuring.Appendix.Listing8LoopTerminalReads
public import SmcTuring.Appendix.Listing8LoopIterationTables

public import SmcTuring.Appendix.Listing8LoopIterationFetch
public import SmcTuring.Appendix.Listing8LoopTerminalFetch

public section
namespace SmcTuring.Appendix.Listing8LoopInterpreterFetch
set_option maxHeartbeats 1000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run StringFetchWindows.Run
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

/-- Logical finite execution ending in a declared halt is realized by the
actual generic body/control iterations, then every transition declaration,
reset/DOHALT instruction and updated input declaration. All future native
images/states/traces are constructed, with every actual classifier/fetch and complete data-read window, original rule-byte and
final tape preservation. Native capacity/placement certificates are explicit. -/
theorem execute (mode : Mode) (origin : Nat) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (l : Layout) (old : OldInput) (state : StringExecution.State mode)
    (ctx : Context mode origin l t g node rule) (image : Listing8LoopHaltImage.Current mode origin l t g node rule old state) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode state code finalState ∧
      StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) code state ∧
      StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ code state ∧
      StringFetchWindows.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩ code state ∧
      finalState.principal.pc.toNat=Listing8GraphLayout.endPC mode origin lastGraph.transitions lastGraph.nodes ∧
      code.length=count*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin lastGraph.transitions)
        (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated lastGraph lastNode lastRule)) finalState.principal.memory ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) finalState.principal.memory ∧
      List.ofFn (fun index : Fin lastGraph.nodes => DwordCode.get finalState.principal.memory (nodePC mode origin lastGraph index+6))=
        List.ofFn (fun index : Fin lastGraph.nodes => ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape index).symbol) ∧
      DwordCode.get finalState.principal.memory (nodePC mode origin lastGraph (Listing8GraphStep.nextNode lastGraph lastNode lastRule)+6)=
        ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape (Listing8GraphStep.nextNode lastGraph lastNode lastRule)).symbol ∧
      finalState.principal.stack=state.principal.stack ∧ finalState.sourceIndex=state.sourceIndex ∧ finalState.destinationIndex=state.destinationIndex ∧
      finalState.backwards=false ∧ finalState.principal.carry=false := by
  obtain ⟨lastL,lastOld,lastState,prefixCode,lastCtx,lastImage,prefixTrace,prefixOwned,prefixReads,prefixFetch,prefixLength,stack,source,destination⟩:=
    Listing8LoopIterationFetch.execute mode origin t logical l old state ctx image
  have tailTrace:=Listing8LoopTerminal.trace mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  have endpoint:=Listing8LoopTerminal.endpoint mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  have tailLength:=Listing8LoopTerminal.instruction_count mode origin lastL t lastGraph lastNode lastRule lastState
  have graph:=Listing8LoopTerminal.source_graph mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  have original:=graph.2
  rw [Listing8TransitionTable.Initial,Listing8LoopIterationTables.table_bytes logical mode origin (Listing8FullTableImage.start mode origin)] at original
  have symbols:=Listing8LoopTerminal.all_symbols mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  have head:=Listing8LoopTerminal.logical_head_output mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  have registers:=Listing8LoopTerminal.registers mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  refine ⟨Listing8LoopTerminal.finish mode origin lastL t lastGraph lastNode lastRule lastState,
    prefixCode++Listing8LoopTerminal.program mode origin lastL t lastGraph lastNode lastRule lastState,
    StringStack.trace_append mode prefixTrace tailTrace,?_,?_,?_,endpoint,?_,graph.1,original,symbols,head,
    registers.1.trans stack,registers.2.2.1.trans source,registers.2.2.2.1.trans destination,registers.2.2.2.2,registers.2.1⟩
  · apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      prefixCode (Listing8LoopTerminal.program mode origin lastL t lastGraph lastNode lastRule lastState)
      state lastState prefixTrace prefixOwned
    have counts := Listing8LoopIterationWrites.counts logical
    rw [←counts.1,←counts.2]
    with_reducible
      exact Listing8LoopTerminalBodyWrites.owned mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  · apply StringReadRuns.append_trace mode _ _ _ state lastState prefixTrace prefixReads
    have counts:=Listing8LoopIterationWrites.counts logical
    rw [←counts.1,←counts.2]
    exact Listing8LoopTerminalReads.contained mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  · apply StringFetchWindows.append_trace mode _ _ _ state lastState prefixTrace prefixFetch
    have counts:=Listing8LoopIterationWrites.counts logical
    rw [←counts.1,←counts.2]
    exact Listing8LoopTerminalFetch.contained mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted
  · rw [List.length_append,prefixLength,tailLength]
    omega

end SmcTuring.Appendix.Listing8LoopInterpreterFetch

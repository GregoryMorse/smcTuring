module
public import SmcTuring.Appendix.Listing8LoopTerminal
public import SmcTuring.Appendix.Listing8LoopTailIteration
public import SmcTuring.Appendix.Listing8LoopIterationTables

public section
namespace SmcTuring.Appendix.Listing8LoopInterpreterTail
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput

theorem counts {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule) :
    lastGraph.transitions=g.transitions ∧ lastGraph.nodes=g.nodes := by
  induction logical with
  | refl => exact ⟨rfl,rfl⟩
  | next selected rest ih => exact ih

/-- Logical finite execution ending in a declared halt is realized by the
actual generic body/control iterations, then every transition declaration,
reset/DOHALT instruction and updated input declaration. All future native
images/states/traces are constructed, with complete original rule-byte and
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
      finalState.backwards=false ∧ finalState.principal.carry=false ∧
      (∀ observed size, Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤observed →
        ByteMemory.bytesAt finalState.principal.memory observed size=ByteMemory.bytesAt state.principal.memory observed size) := by
  obtain ⟨lastL,lastOld,lastState,prefixCode,lastCtx,lastImage,prefixTrace,prefixLength,stack,source,destination,prefixFrames⟩:=
    Listing8LoopTailIteration.execute mode origin t logical l old state ctx image
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
    StringStack.trace_append mode prefixTrace tailTrace,endpoint,?_,graph.1,original,symbols,head,
    registers.1.trans stack,registers.2.2.1.trans source,registers.2.2.2.1.trans destination,registers.2.2.2.2,registers.2.1,?_⟩
  · rw [List.length_append,prefixLength,tailLength]
    omega
  · have counts:=counts logical
    intro observed size after
    have lastAfter : Listing8GraphLayout.endPC mode origin lastGraph.transitions lastGraph.nodes≤observed := by
      rw [counts.1,counts.2];exact after
    exact (Listing8LoopTailFrames.terminal mode origin lastL t lastGraph lastNode lastRule lastCtx lastOld lastState lastImage halted observed size lastAfter).trans (prefixFrames observed size after)

end SmcTuring.Appendix.Listing8LoopInterpreterTail

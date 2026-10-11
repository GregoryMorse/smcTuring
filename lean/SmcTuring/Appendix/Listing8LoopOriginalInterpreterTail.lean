module
public import SmcTuring.Appendix.Listing8LoopOriginalTailFrames

public section
namespace SmcTuring.Appendix.Listing8LoopOriginalInterpreterTail
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

/-- The actual complete finite Listing 8 execution from one original
initialization, including immediate original halt and all trailing declarations.
Only logical steps, a declared final halt and static native placement/resources
are inputs. Every future native state, packet and trace is constructed. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode origin l t g node rule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) code finalState ∧
      finalState.principal.pc.toNat=Listing8GraphLayout.endPC mode origin lastGraph.transitions lastGraph.nodes ∧
      code.length=(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+(if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes ∧
      Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin lastGraph.transitions)
        (Listing8GraphNodeImage.declarations mode origin (Listing8GraphStep.updated lastGraph lastNode lastRule)) finalState.principal.memory ∧
      Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) finalState.principal.memory ∧
      List.ofFn (fun index : Fin lastGraph.nodes => DwordCode.get finalState.principal.memory (nodePC mode origin lastGraph index+6))=
        List.ofFn (fun index : Fin lastGraph.nodes => ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape index).symbol) ∧
      DwordCode.get finalState.principal.memory (nodePC mode origin lastGraph (Listing8GraphStep.nextNode lastGraph lastNode lastRule)+6)=
        ((Listing8GraphStep.updated lastGraph lastNode lastRule).tape (Listing8GraphStep.nextNode lastGraph lastNode lastRule)).symbol ∧
      finalState.principal.stack=seed.principal.stack ∧ finalState.sourceIndex=seed.sourceIndex ∧ finalState.destinationIndex=seed.destinationIndex ∧
      finalState.backwards=false ∧ finalState.principal.carry=false ∧
      (∀ observed size, Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤observed →
        ByteMemory.bytesAt finalState.principal.memory observed size=ByteMemory.bytesAt memory observed size) := by
  cases logical with
  | refl =>
    have graph:=Listing8LoopFirstHalt.source_graph mode origin l t g node rule ctx memory seed halted
    have registers:=Listing8LoopFirstHalt.registers mode origin l t g node rule ctx memory seed halted
    refine ⟨Listing8LoopFirstHalt.finish mode origin l t g node rule memory seed,
      Listing8LoopFirstHalt.program mode origin l t g node rule memory seed,
      Listing8LoopFirstHalt.trace mode origin l t g node rule ctx memory seed halted,
      Listing8LoopFirstHalt.endpoint mode origin l t g node rule ctx memory seed halted,?_,graph.1,graph.2,
      Listing8LoopFirstHalt.all_symbols mode origin l t g node rule ctx memory seed halted,
      Listing8LoopFirstHalt.logical_head_output mode origin l t g node rule ctx memory seed halted,
      registers.1,registers.2.2.1,registers.2.2.2.1,registers.2.2.2.2,registers.2.1,Listing8LoopOriginalTailFrames.first_halt_window mode origin l t g node rule ctx memory seed halted⟩
    rw [Listing8LoopFirstHalt.instruction_count,Nat.zero_mul]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
  | @next g node rule target count lastGraph lastNode lastRule selected rest =>
    have nonhalt : ¬Listing8GraphRun.Halted g node rule := by
      intro firstHalted
      have none:=(Listing8GraphStep.halted_iff g node rule).mpr firstHalted
      rw [selected] at none
      cases none
    have first:=Listing8GraphBackedge.trace mode origin l t g node rule ctx memory seed nonhalt
    have registers:=Listing8GraphBackedge.registers mode origin l t g node rule ctx memory seed
    obtain ⟨finalState,tail,actual,endpoint,length,nodes,rules,symbols,head,stack,source,destination,forward,carry,frames⟩:=
      Listing8LoopInterpreterTail.execute mode origin t rest halted (Listing8GraphMacroImages.nextLayout mode origin l g node rule target)
        (Listing8LoopGraphBackedgeFailure.old mode origin g node rule) (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
        (Listing8LoopGraphContext.next mode origin l t g node rule target ctx)
        (Listing8LoopHaltImage.after_backedge mode origin l t g node rule target ctx selected memory seed)
    have original:=rules
    rw [Listing8TransitionTable.Initial,Listing8MainGraphTable.updated_table_bytes] at original
    refine ⟨finalState,Listing8GraphBackedge.program mode origin l t g node rule memory seed++tail,
      StringStack.trace_append mode first actual,endpoint,?_,nodes,original,symbols,head,
      stack.trans registers.2.1,source.trans registers.2.2.1,destination.trans registers.2.2.2.1,forward,carry,?_⟩
    · rw [List.length_append,Listing8GraphBackedge.instruction_count,length,Nat.add_mul,Nat.one_mul]
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega
    · intro observed size after
      exact (frames observed size after).trans (Listing8LoopOriginalTailFrames.backedge_window mode origin l t g node rule ctx memory seed observed size after)

end SmcTuring.Appendix.Listing8LoopOriginalInterpreterTail

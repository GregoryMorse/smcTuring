module
public import SmcTuring.Appendix.Listing8GlobalMaintainedInterpreterTemplates
public import SmcTuring.Appendix.Listing8GlobalOriginalTerminalTemplates

public section
namespace SmcTuring.Appendix.Listing8GlobalOriginalInterpreterTemplates
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

/-- One original emission supplies bootstrap, first branch, all maintained
iterations, terminal table/reset and every node declaration. Logical source
steps and static placement are the only execution inputs; every later native
state/image/trace is constructed. Immediate original halt is included. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    {g : Graph} {node : Fin g.nodes} {rule : Fin g.transitions} {count : Nat}
    {lastGraph : Graph} {lastNode : Fin lastGraph.nodes} {lastRule : Fin lastGraph.transitions}
    (logical : Listing8LoopIteration.Steps g node rule count lastGraph lastNode lastRule)
    (halted : Listing8GraphRun.Halted lastGraph lastNode lastRule)
    (ctx : Context mode origin l t g node rule) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∃ (finalState : StringExecution.State mode) (code : List (StringStack.Form mode)),
      StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) code finalState ∧
      StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
        code (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) ∧
      Listing8GlobalControlTemplates.Property mode origin finalState.principal.memory ∧
      finalState.principal.pc.toNat=Listing8GraphLayout.endPC mode origin lastGraph.transitions lastGraph.nodes ∧
      code.length=(if mode=.x86 then 8 else 13)+count*(if mode=.x86 then 139 else 182)+
        (if mode=.x86 then 148 else 194)+11*lastGraph.transitions+9*lastGraph.nodes := by
  cases logical with
  | refl =>
    have terminal:=Listing8GlobalOriginalTerminalTemplates.execute mode origin l t g node rule ctx memory seed halted
    refine ⟨Listing8LoopFirstHalt.finish mode origin l t g node rule memory seed,
      Listing8GraphHaltTerminalWrites.program mode origin l t g node rule memory seed,terminal.1,terminal.2,
      Listing8GlobalOriginalTerminalTemplates.property mode origin l t g node rule ctx memory seed halted,
      Listing8LoopFirstHalt.endpoint mode origin l t g node rule ctx memory seed halted,?_⟩
    rw [Listing8GraphHaltTerminalWrites.instruction_count,Nat.zero_mul]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false]
  | @next g node rule target count lastGraph lastNode lastRule selected rest =>
    have nonhalt : ¬Listing8GraphRun.Halted g node rule := by
      intro stopped
      have missing:=(Listing8GraphStep.halted_iff g node rule).mpr stopped
      rw [selected] at missing
      cases missing
    have first:=Listing8GraphReturnWrites.trace mode origin l t g node rule ctx memory seed nonhalt
    have templates:=Listing8GlobalOriginalControlTemplates.nonhalt mode origin l t g node rule ctx memory seed nonhalt
    obtain ⟨finalState,tail,actual,tailTemplates,property,endpoint,length⟩:=
      Listing8GlobalMaintainedInterpreterTemplates.execute mode origin t rest halted
        (nextLayout mode origin l g node rule target) (Listing8LoopGraphBackedgeFailure.old mode origin g node rule)
        (Listing8GraphBackedge.finish mode origin l t g node rule memory seed)
        (Listing8LoopGraphContext.next mode origin l t g node rule target ctx)
        (Listing8LoopHaltImage.after_backedge mode origin l t g node rule target ctx selected memory seed)
    refine ⟨finalState,Listing8GraphReturnWrites.program mode origin l t g node rule memory seed++tail,
      StringStack.trace_append mode first actual,?_,property,endpoint,?_⟩
    · rw [StringTemplateStates.append,StringWrites.trace_run_eq mode first]
      exact ⟨templates,tailTemplates⟩
    · rw [List.length_append,Listing8GraphReturnWrites.instruction_count,length,Nat.add_mul,Nat.one_mul]
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> omega

end SmcTuring.Appendix.Listing8GlobalOriginalInterpreterTemplates

module
public import SmcTuring.Appendix.Listing4EntrySlotRegions
public import SmcTuring.Appendix.Listing8GlobalInitialControl
public import SmcTuring.Appendix.Listing8GlobalOriginalBodyRegions
public import SmcTuring.Appendix.Listing8GraphJumpWrites
public import SmcTuring.Appendix.Listing8GraphReturnWrites

public section
namespace SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates
set_option maxHeartbeats 2000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
attribute [local irreducible] StringStoreRegions.Run StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphFailureWrites.program mode origin l t g node rule memory seed++
    Listing8JumpReturn.program mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed)
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8JumpReturn.finish mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed)
    (Listing8GraphFailureWrites.finish mode origin l t g node rule memory seed)

theorem body_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      (Listing8GraphFailureWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  have boot:=Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  change StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
    (Listing4EntryLayout.forms mode origin) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) at boot
  have first:=BoundedStoreRegions.monotone mode (Listing4StackTemplates.Slots mode origin) (Listing8GlobalControlLayout.Allowed mode origin)
    (Listing4EntryLayout.forms mode origin) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
    (fun _ _ slots => Or.inl slots)
    (Listing4EntrySlotRegions.entry mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))
  rw [Listing8GraphFailureWrites.program,StringStoreRegions.append,StringWrites.trace_run_eq mode boot]
  exact ⟨first,Listing8GlobalOriginalBodyRegions.failure mode origin l t g node rule ctx memory seed⟩

theorem body_decodes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8GraphFailureWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  Listing8GlobalControlTemplates.all_decodes mode origin _ _
    (Listing8GlobalControlTemplates.initial mode origin _ (Listing8GlobalInitialControl.current mode origin l t g node rule ctx memory seed))
    (body_regions mode origin l t g node rule ctx memory seed)

theorem return_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8JumpReturn.Current mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed)
      (Listing8GraphFailureWrites.finish mode origin l t g node rule memory seed).principal.memory := by
  have current:=Listing8ControlTemplateBindings.original_current mode origin l t (values mode origin g node rule)
    (nodePC mode origin g g.halt) (Listing8FullTableImage.start mode origin) ctx.resources (owners mode origin l t g node rule ctx)
    ctx.copies ctx.boot ctx.body (Listing8GraphNextFailImage.tail_bounds mode origin l t g node rule ctx)
    (Listing8FullTableImage.backing mode origin (table mode origin g)
      (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g)
        (Listing8GraphNodeImage.image mode origin g memory))) seed
  change Listing8JumpReturn.Current mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed)
    (Listing8GlobalJump.bodyEnd mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8GraphBackedge.backing mode origin l g memory) seed).principal.memory at current
  rw [←Listing8GraphJumpWrites.failure_state mode origin l t g node rule ctx memory seed] at current
  exact current

theorem return_entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing8GraphFailureWrites.finish mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin) := by
  rw [Listing8GraphJumpWrites.failure_state mode origin l t g node rule ctx memory seed]
  exact Listing8GlobalBoot.endpoint mode origin l t _ _ ctx.resources (owners mode origin l t g node rule ctx)
    ctx.copies ctx.boot ctx.body (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed

theorem target_capacity (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) (failed : Bool) :
    Listing8JumpReturn.target mode origin failed+Listing4TargetLayout.size mode<2^(8*mode.wordBytes) := by
  cases failed
  · exact Listing4EntryLayout.target_capacity mode origin (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  · exact Listing8FailLayout.capacity mode origin l _ (Listing8GraphNextFailImage.tail_bounds mode origin l t g node rule ctx)

/-- The complete original bootstrap/main/CALL/selected-target execution is
constructed from one emitted initial image. Every global descriptor decodes
at the same every prefix, including both possible source-derived branches. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) ∧
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  have first:=(Listing8GraphFailureWrites.execute mode origin l t g node rule ctx memory seed).1
  have last:=Listing8JumpReturn.trace mode origin _ _ (return_entry mode origin l t g node rule ctx memory seed)
    (Listing8JumpImage.capacity mode origin l t _ ctx.boot ctx.body)
    (target_capacity mode origin l t g node rule ctx _) (return_current mode origin l t g node rule ctx memory seed)
  refine ⟨StringStack.trace_append mode first last,?_⟩
  rw [program,StringTemplateStates.append,StringWrites.trace_run_eq mode first]
  constructor
  · exact body_decodes mode origin l t g node rule ctx memory seed
  · rw [Listing8GraphJumpWrites.failure_state mode origin l t g node rule ctx memory seed]
    exact Listing8GlobalControlBindings.original_jump mode origin l t (values mode origin g node rule)
      (nodePC mode origin g g.halt) (Listing8FullTableImage.start mode origin) ctx.resources (owners mode origin l t g node rule ctx)
      ctx.copies ctx.boot ctx.body (Listing8GraphNextFailImage.tail_bounds mode origin l t g node rule ctx)
      (Listing8FullTableImage.backing mode origin (table mode origin g)
        (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g)
          (Listing8GraphNodeImage.image mode origin g memory))) seed

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=if mode=.x86 then 147 else 195 := by
  rw [program,List.length_append,Listing8GraphFailureWrites.instruction_count,Listing8JumpReturn.instruction_count]
  cases mode <;> rfl

theorem nonhalt (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    StringTemplateStates.Run mode (fun reached => Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory)
      (Listing8GraphReturnWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  StringStackTraceDeterminism.transport mode _ _ _ _ _ _
    (by rw [instruction_count,Listing8GraphReturnWrites.instruction_count])
    (execute mode origin l t g node rule ctx memory seed).1
    (Listing8GraphReturnWrites.trace mode origin l t g node rule ctx memory seed nonhalt)
    (execute mode origin l t g node rule ctx memory seed).2

end SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates

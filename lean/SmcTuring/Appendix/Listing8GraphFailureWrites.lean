module
public import SmcTuring.Appendix.Listing8GraphStateWrites
public import SmcTuring.Appendix.Listing8FailureWrites

public section
namespace SmcTuring.Appendix.Listing8GraphFailureWrites
set_option maxHeartbeats 1000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def region (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) :=
  Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
@[expose] def forms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphStateWrites.forms mode origin l t g node rule memory seed++
    (Listing8FailureTrace.program mode (region mode origin l g)
      (Listing8GraphStateWrites.finish mode origin l t g node rule memory seed)).map StringStack.Form.previous
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing4EntryLayout.forms mode origin++forms mode origin l t g node rule memory seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailureImage.finish mode (region mode origin l g)
    (Listing8GraphStateWrites.finish mode origin l t g node rule memory seed)

theorem placement (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8FailureWrites.Placement mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) (region mode origin l g) := by
  have lower:=(Listing8GraphCopyWriteBounds.lower mode origin l t g node rule ctx).1
  have body:=Listing8FailureGeometry.positions mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.body
  have call:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
    (Listing8LoopTailGeometry.input_before_end mode origin g)
  have cursor:=Listing8GraphStateWrites.cursor_bounds mode origin l t g node rule ctx
  have sentinel:=Listing8GraphFieldWriteBounds.node_word mode origin g g.halt ctx.native
  unfold StringWrites.WordOwned at sentinel
  rw [Listing8GraphPointers.node_toNat mode origin g g.halt ctx.native] at sentinel
  refine ⟨⟨?_,call⟩,cursor,sentinel⟩
  change origin≤(Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at body <;> omega

theorem state_state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphStateWrites.finish mode origin l t g node rule memory seed=
      Listing8GlobalFailure.entryState mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
        (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed) := by
  unfold Listing8GraphStateWrites.finish Listing8GlobalFailure.entryState Listing8GlobalState.finish
  rw [Listing8GraphStateWrites.head_state mode origin l t g node rule ctx memory seed]
  rfl

set_option maxHeartbeats 1000000 in
theorem state_run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.run mode (Listing8GraphStateWrites.forms mode origin l t g node rule memory seed)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)=
        Listing8GraphStateWrites.finish mode origin l t g node rule memory seed := by
  have actual:=StringWrites.trace_run_eq mode (Listing8GraphStateWrites.execute mode origin l t g node rule ctx memory seed).1
  have bootRun:=StringWrites.trace_run_eq mode (Listing4Entry.trace mode origin
    (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))
  change StringWrites.run mode (Listing4EntryLayout.forms mode origin)
    (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)=Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed at bootRun
  rw [Listing8GraphStateWrites.program,StringWrites.run_append,bootRun] at actual
  exact actual

set_option maxHeartbeats 1000000 in
theorem failure_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8FailureTrace.program mode (region mode origin l g)
        (Listing8GraphStateWrites.finish mode origin l t g node rule memory seed)).map StringStack.Form.previous)
      (Listing8GraphStateWrites.finish mode origin l t g node rule memory seed) := by
  have current:=Listing8FailureGlobalImage.current_region mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body
    (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  change Listing8FailureImage.Initial mode (region mode origin l g)
    (Listing8GlobalFailure.entryState mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory at current
  rw [←state_state mode origin l t g node rule ctx memory seed] at current
  exact Listing8FailureWrites.owned mode origin _ (region mode origin l g)
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) (placement mode origin l t g node rule ctx)
    (Listing8GraphStateWrites.finish mode origin l t g node rule memory seed)
    (Listing8GraphStateWrites.endpoint mode origin l t g node rule ctx memory seed) current

theorem body_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  rw [forms,StringWrites.owned_run_append,state_run mode origin l t g node rule ctx memory seed]
  exact ⟨Listing8GraphStateWrites.body_owned mode origin l t g node rule ctx memory seed,
    failure_owned mode origin l t g node rule ctx memory seed⟩

set_option maxHeartbeats 1000000 in
/-- The one original initialized trace now reaches the patched CALL operand.
Every 132/173 reached body instruction has a complete code-owned store. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have current:=Listing8FailureGlobalImage.current_region mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body
    (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  change Listing8FailureImage.Initial mode (region mode origin l g)
    (Listing8GlobalFailure.entryState mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory at current
  rw [←state_state mode origin l t g node rule ctx memory seed] at current
  have last:=StringStack.previous_trace mode (Listing8FailureTrace.trace mode (region mode origin l g)
    (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body)
    (Listing8GraphStateWrites.finish mode origin l t g node rule memory seed)
    (Listing8GraphStateWrites.endpoint mode origin l t g node rule ctx memory seed) current)
  have first:=(Listing8GraphStateWrites.execute mode origin l t g node rule ctx memory seed).1
  refine ⟨?_,body_owned mode origin l t g node rule ctx memory seed⟩
  simpa only [program,forms,finish,Listing8GraphStateWrites.program,List.append_assoc] using StringStack.trace_append mode first last

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=if mode=.x86 then 140 else 186 := by
  have prior:=Listing8GraphStateWrites.instruction_count mode origin l t g node rule memory seed
  rw [Listing8GraphStateWrites.program,List.length_append] at prior
  rw [program,List.length_append,forms,List.length_append,List.length_map,Listing8FailureTrace.instruction_count]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at prior ⊢ <;> omega

set_option maxHeartbeats 1000000 in
theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8FailureLayout.endPC mode (region mode origin l g)) := by
  have current:=Listing8FailureGlobalImage.current_region mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin) ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body
    (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  change Listing8FailureImage.Initial mode (region mode origin l g)
    (Listing8GlobalFailure.entryState mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
      (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory at current
  rw [←state_state mode origin l t g node rule ctx memory seed] at current
  exact Listing8FailureTrace.endpoint mode _ (Listing8FailureGeometry.local_bounds mode l t _ _ ctx.resources ctx.body) _
    (Listing8GraphStateWrites.endpoint mode origin l t g node rule ctx memory seed) current

end SmcTuring.Appendix.Listing8GraphFailureWrites

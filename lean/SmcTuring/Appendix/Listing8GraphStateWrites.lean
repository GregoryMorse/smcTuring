module
public import SmcTuring.Appendix.Listing8GraphHeadWrites
public import SmcTuring.Appendix.Listing8StateWrites

public section
namespace SmcTuring.Appendix.Listing8GraphStateWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def failureBacking (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8FailureGlobalImage.backing mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory)
@[expose] def forms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphHeadWrites.forms mode origin l t g node rule memory seed++
    (Listing8StateTrace.program mode (Listing8StateGeometry.region mode l)
      (Listing8GraphHeadWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing4EntryLayout.forms mode origin++forms mode origin l t g node rule memory seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8StateTrace.finish mode (Listing8StateGeometry.region mode l)
    (Listing8GraphHeadWrites.finish mode origin l t g node rule memory seed)

theorem region_bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    origin≤(Listing8StateGeometry.region mode l).start ∧
      Listing8StateLayout.endPC mode (Listing8StateGeometry.region mode l)≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  have lower:=(Listing8GraphCopyWriteBounds.lower mode origin l t g node rule ctx).1
  have state:=Listing8StateGeometry.positions mode l t ctx.body.state
  have body:=Listing8FailureGeometry.positions mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.body
  have call:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
    (Listing8LoopTailGeometry.input_before_end mode origin g)
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at state body <;> constructor <;> omega

theorem cursor_bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    origin≤(Listing8StateGeometry.region mode l).cursor ∧
      (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes :=
  (Listing8GraphPointerWriteBounds.word mode origin l t g node rule ctx).2

theorem head_state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphHeadWrites.finish mode origin l t g node rule memory seed=
      Listing8GlobalState.entryState mode l t (values mode origin g node rule)
        (failureBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed) := by
  unfold Listing8GraphHeadWrites.finish Listing8GlobalState.entryState Listing8GlobalHead.finish
  rw [Listing8GraphHeadWrites.direction_state mode origin l t g node rule ctx memory seed]
  rfl

theorem head_run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.run mode (Listing8GraphHeadWrites.forms mode origin l t g node rule memory seed)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)=
        Listing8GraphHeadWrites.finish mode origin l t g node rule memory seed := by
  have actual:=StringDwordWritesBridge.trace mode (Listing8GlobalHead.trace mode l t _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head
    (Listing8GraphDirectionWrites.tailBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
  unfold Listing8GlobalHead.program Listing8GlobalHead.finish at actual
  rw [List.map_append,←Listing8GraphHeadWrites.direction_state mode origin l t g node rule ctx memory seed] at actual
  unfold Listing8GlobalDirection.program at actual
  rw [List.map_append,←Listing8GraphDirectionWrites.input_state mode origin l t g node rule ctx memory seed] at actual
  change StringStack.Trace mode
    (initial mode l (values mode origin g node rule) (Listing8GraphCopyWrites.copyBacking mode origin l t g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
    (Listing8GraphHeadWrites.forms mode origin l t g node rule memory seed)
    (Listing8GraphHeadWrites.finish mode origin l t g node rule memory seed) at actual
  rw [←Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed] at actual
  exact StringWrites.trace_run_eq mode actual

theorem state_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8StateTrace.program mode (Listing8StateGeometry.region mode l)
        (Listing8GraphHeadWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphHeadWrites.finish mode origin l t g node rule memory seed) :=
  Listing8StateWrites.owned mode origin _ (Listing8StateGeometry.region mode l)
    (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state)
    (region_bounds mode origin l t g node rule ctx) (cursor_bounds mode origin l t g node rule ctx) _
    (Listing8GraphHeadWrites.endpoint mode origin l t g node rule ctx memory seed)

theorem body_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  rw [forms,StringWrites.owned_run_append,head_run mode origin l t g node rule ctx memory seed]
  exact ⟨Listing8GraphHeadWrites.body_owned mode origin l t g node rule ctx memory seed,
    state_owned mode origin l t g node rule ctx memory seed⟩

set_option maxHeartbeats 1000000 in
/-- One original initialization and bootstrap now execute every head and
state update, with all 119/157 reached body instructions code-owned. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have current:=Listing8StateImage.helper_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state
    (failureBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  have headers:=Listing8StateImage.headers_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state
    (failureBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  change ByteMemory.bytesAt (Listing8GlobalState.entryState mode l t (values mode origin g node rule)
    (failureBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory _ _=_ at current
  change DwordPackets.Intact mode _ (Listing8GlobalState.entryState mode l t (values mode origin g node rule)
    (failureBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)).principal.memory at headers
  rw [←head_state mode origin l t g node rule ctx memory seed] at current headers
  have last:=StringDwordWritesBridge.trace mode (Listing8StateTrace.trace mode (Listing8StateGeometry.region mode l)
    (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state)
    (Listing8GraphHeadWrites.finish mode origin l t g node rule memory seed)
    (Listing8GraphHeadWrites.endpoint mode origin l t g node rule ctx memory seed) current headers)
  have first:=(Listing8GraphHeadWrites.execute mode origin l t g node rule ctx memory seed).1
  refine ⟨?_,body_owned mode origin l t g node rule ctx memory seed⟩
  simpa only [program,forms,finish,Listing8GraphHeadWrites.program,List.append_assoc] using StringStack.trace_append mode first last

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=if mode=.x86 then 127 else 170 := by
  have prior:=Listing8GraphHeadWrites.instruction_count mode origin l t g node rule memory seed
  rw [Listing8GraphHeadWrites.program,List.length_append] at prior
  rw [program,List.length_append,forms,List.length_append,List.length_map,Listing8StateTrace.instruction_count]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at prior ⊢ <;> omega

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8StateLayout.endPC mode (Listing8StateGeometry.region mode l)) :=
  Listing8StateTrace.endpoint mode _ (Listing8StateGeometry.local_bounds mode l t ctx.resources ctx.body.state) _
    (Listing8GraphHeadWrites.endpoint mode origin l t g node rule ctx memory seed)

end SmcTuring.Appendix.Listing8GraphStateWrites

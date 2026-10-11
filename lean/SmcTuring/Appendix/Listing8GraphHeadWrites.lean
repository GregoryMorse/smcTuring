module
public import SmcTuring.Appendix.Listing8GraphDirectionWrites
public import SmcTuring.Appendix.Listing8HeadTailWrites

public section
namespace SmcTuring.Appendix.Listing8GraphHeadWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def forms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphDirectionWrites.forms mode origin l t g node rule memory seed++
    (Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l)
      (Listing8GraphDirectionWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing4EntryLayout.forms mode origin++forms mode origin l t g node rule memory seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8HeadTailTrace.finish mode (Listing8DirectionGeometry.region mode l)
    (Listing8GraphDirectionWrites.finish mode origin l t g node rule memory seed)

theorem direction_state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphDirectionWrites.finish mode origin l t g node rule memory seed=
      Listing8GlobalHead.entryState mode l t (values mode origin g node rule)
        (Listing8GraphDirectionWrites.tailBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed) := by
  unfold Listing8GraphDirectionWrites.finish Listing8GlobalHead.entryState Listing8GlobalDirection.finish
  rw [Listing8GraphDirectionWrites.input_state mode origin l t g node rule ctx memory seed]

theorem direction_run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.run mode (Listing8GraphDirectionWrites.forms mode origin l t g node rule memory seed)
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)=
        Listing8GraphDirectionWrites.finish mode origin l t g node rule memory seed := by
  have actual:=StringDwordWritesBridge.trace mode (Listing8GlobalDirection.trace mode l t _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head
    (Listing8GraphDirectionWrites.tailBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
  unfold Listing8GlobalDirection.program Listing8GlobalDirection.finish at actual
  rw [List.map_append,←Listing8GraphDirectionWrites.input_state mode origin l t g node rule ctx memory seed] at actual
  change StringStack.Trace mode
    (initial mode l (values mode origin g node rule) (Listing8GraphCopyWrites.copyBacking mode origin l t g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
    (Listing8GraphDirectionWrites.forms mode origin l t g node rule memory seed)
    (Listing8GraphDirectionWrites.finish mode origin l t g node rule memory seed) at actual
  rw [←Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed] at actual
  exact StringWrites.trace_run_eq mode actual

theorem head_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l)
        (Listing8GraphDirectionWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphDirectionWrites.finish mode origin l t g node rule memory seed) :=
  Listing8HeadTailWrites.owned mode origin _ (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head)
    (Listing8GraphDirectionWrites.region_bounds mode origin l t g node rule ctx)
    (Listing8GraphInputWriteBounds.cursor_tape mode origin l t g node rule ctx).1 _
    (Listing8GraphDirectionWrites.endpoint mode origin l t g node rule ctx memory seed)

theorem body_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  rw [forms,StringWrites.owned_run_append,direction_run mode origin l t g node rule ctx memory seed]
  exact ⟨Listing8GraphDirectionWrites.body_owned mode origin l t g node rule ctx memory seed,
    head_owned mode origin l t g node rule ctx memory seed⟩

/-- The original image and actual bootstrap extend through both complete
head halves, with all 113/145 reached body instructions code-owned. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have current:=Listing8HeadImage.xor_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head
    (Listing8GraphDirectionWrites.tailBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  have headers:=Listing8HeadImage.headers_current mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head
    (Listing8GraphDirectionWrites.tailBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  change ByteMemory.bytesAt (Listing8GlobalHead.entryState mode l t _ _ _).principal.memory _ _=_ at current
  change DwordPackets.Intact mode _ (Listing8GlobalHead.entryState mode l t _ _ _).principal.memory at headers
  rw [←direction_state mode origin l t g node rule ctx memory seed] at current headers
  have last:=StringDwordWritesBridge.trace mode (Listing8HeadTailTrace.trace mode (Listing8DirectionGeometry.region mode l)
    (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) _
    (Listing8GraphDirectionWrites.endpoint mode origin l t g node rule ctx memory seed) current headers)
  have first:=(Listing8GraphDirectionWrites.execute mode origin l t g node rule ctx memory seed).1
  refine ⟨?_,body_owned mode origin l t g node rule ctx memory seed⟩
  simpa only [program,forms,finish,Listing8GraphDirectionWrites.program,List.append_assoc] using StringStack.trace_append mode first last

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=if mode=.x86 then 121 else 158 := by
  have prior:=Listing8GraphDirectionWrites.instruction_count mode origin l t g node rule memory seed
  rw [Listing8GraphDirectionWrites.program,List.length_append] at prior
  rw [program,List.length_append,forms,List.length_append,List.length_map,Listing8HeadTailTrace.instruction_count]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at prior ⊢ <;> omega

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)) :=
  Listing8HeadTailTrace.endpoint mode _ (Listing8HeadGeometry.tail_bounds mode l t ctx.body.state.head) _
    (Listing8GraphDirectionWrites.endpoint mode origin l t g node rule ctx memory seed)

end SmcTuring.Appendix.Listing8GraphHeadWrites

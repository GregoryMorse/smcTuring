module
public import SmcTuring.Appendix.Listing8GraphInputWriteBounds
public import SmcTuring.Appendix.Listing8GraphPointerWrites

public section
namespace SmcTuring.Appendix.Listing8GraphInputWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def forms (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :=
  (Listing8GlobalInput.program mode l t v).map (StringStoreWrites.liftDword mode)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  Listing4EntryLayout.forms mode origin++forms mode l t (values mode origin g node rule)
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  let state:=Listing8GraphPointerWrites.finish mode origin l t g node rule memory seed
  {state with principal:=(Listing8LiteralComposition.finish mode l.input (values mode origin g node rule).rule
      (values mode origin g node rule).tape (values mode origin g node rule).fresh state.principal)}

/-- The actual original execution reaches the same state used by the
global input theorem; no host reinitialization or future image is assumed. -/
theorem pointer_state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphPointerWrites.finish mode origin l t g node rule memory seed=
      Listing8GlobalInput.entryState mode l t (values mode origin g node rule)
        (Listing8GraphPointerWrites.helperBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed) := by
  unfold Listing8GraphPointerWrites.finish Listing8GraphCopiedWrites.finish
  rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
  rfl

theorem pointer_run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.run mode (Listing8GraphPointerWrites.forms mode l t (values mode origin g node rule))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)=
        Listing8GraphPointerWrites.finish mode origin l t g node rule memory seed := by
  rw [pointer_state mode origin l t g node rule ctx memory seed,Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
  exact StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (Listing8PointerImage.trace mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies
      ctx.body.state.head.input.joined (Listing8GraphPointerWrites.helperBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)))

theorem input_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (((Listing8LiteralComposition.program mode l.input (values mode origin g node rule).rule
        (values mode origin g node rule).tape (values mode origin g node rule).fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphPointerWrites.finish mode origin l t g node rule memory seed) := by
  rw [pointer_state mode origin l t g node rule ctx memory seed]
  exact Listing8LiteralInputWrites.mask_canonical_owned mode origin _ l.input
    (Listing8GraphInputWriteBounds.placement mode origin l t g node rule ctx) _ _ force _ force ctx.resources.inputFits
    (Listing8InputBounds.masks mode l ctx.body.state.head.input.fields)
    (Listing8InputBounds.update mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources)
    (Listing8InputBounds.outside mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources) _
    (Listing8GlobalInput.entry mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input _ _)
    (Listing8GlobalInput.input_image mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input _ _)
    (Listing8GlobalInput.cursor mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input _ _)

/-- All transfers, copied owners, pointer copies and literal input operations
own every reached architectural store in the original emitted graph code. -/
theorem body_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode l t (values mode origin g node rule)) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have first:=Listing8GraphPointerWrites.body_owned mode origin l t g node rule ctx memory seed
  have last:=input_owned mode origin l t g node rule ctx memory seed
  have executed:=pointer_run mode origin l t g node rule ctx memory seed
  change StringWrites.run mode ((Listing8PointerImage.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
    (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)=_ at executed
  rw [forms,Listing8GlobalInput.program,List.map_append,StringWrites.owned_run_append,executed]
  exact ⟨first,last⟩

/-- One original initialization and the actual bootstrap run through the
printed input phase. All 101/118 body stores have complete code ownership. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule) (finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode l t (values mode origin g node rule)) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have boot:=Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  have actual:=StringDwordWritesBridge.trace mode (Listing8GlobalInput.trace mode l t _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input
    (Listing8GraphPointerWrites.helperBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
  have sameFinish : Listing8GlobalInput.finish mode l t (values mode origin g node rule)
      (Listing8GraphPointerWrites.helperBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)=
        finish mode origin l t g node rule memory seed := by
    unfold Listing8GlobalInput.finish
    rw [←pointer_state mode origin l t g node rule ctx memory seed]
    rfl
  rw [sameFinish] at actual
  change StringStack.Trace mode
    (initial mode l (values mode origin g node rule) (Listing8GraphCopyWrites.copyBacking mode origin l t g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
    (forms mode l t (values mode origin g node rule)) (finish mode origin l t g node rule memory seed) at actual
  rw [←Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed] at actual
  exact ⟨StringStack.trace_append mode boot actual,body_owned mode origin l t g node rule ctx memory seed⟩

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (program mode origin l t g node rule).length=if mode=.x86 then 109 else 131 := by
  rw [program,List.length_append,forms,List.length_map,Listing4EntryLayout.instruction_count,Listing8GlobalInput.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode (Listing8LiteralInput.endPC mode l.input) := by
  have actual:=Listing8GlobalInput.endpoint mode l t (values mode origin g node rule) ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head.input
    (Listing8GraphPointerWrites.helperBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  unfold Listing8GlobalInput.finish at actual
  rw [←pointer_state mode origin l t g node rule ctx memory seed] at actual
  exact actual

end SmcTuring.Appendix.Listing8GraphInputWrites

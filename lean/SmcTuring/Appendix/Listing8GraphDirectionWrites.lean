module
public import SmcTuring.Appendix.Listing8GraphInputWrites
public import SmcTuring.Appendix.Listing8DirectionWrites

public section
namespace SmcTuring.Appendix.Listing8GraphDirectionWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def tailBacking (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8StateImage.backing mode l (Listing8FailureGlobalImage.backing mode l (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory))
@[expose] def forms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphInputWrites.forms mode l t (values mode origin g node rule)++
    (Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l)
      (Listing8GraphInputWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing4EntryLayout.forms mode origin++forms mode origin l t g node rule memory seed
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8DirectionTrace.finish mode (Listing8DirectionGeometry.region mode l)
    (Listing8GraphInputWrites.finish mode origin l t g node rule memory seed)

theorem region_bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    origin≤(Listing8DirectionGeometry.region mode l).start ∧
      Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)≤Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  have input:=Listing8GraphFieldWriteBounds.input mode origin l t g node rule ctx
  have inputPositions:=Listing8InputBounds.positions mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined
  have direction:=Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)
  have body:=Listing8FailureGeometry.positions mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.body
  have call:=Nat.le_trans (Listing8GraphInputInitial.call_before_input mode origin l t g node rule ctx)
    (Listing8LoopTailGeometry.input_before_end mode origin g)
  change origin≤Listing8LiteralInput.endPC mode l.input ∧ _
  have ending:=direction.2.2.2.2.2.2.2
  change Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l)=
    Listing8LiteralInput.endPC mode l.input+(if mode=.x86 then 91 else 202) at ending
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at inputPositions ending body <;> constructor <;> omega

theorem input_state (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphInputWrites.finish mode origin l t g node rule memory seed=
      Listing8GlobalDirection.entryState mode l t (values mode origin g node rule)
        (tailBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed) := by
  unfold Listing8GraphInputWrites.finish Listing8GlobalDirection.entryState Listing8GlobalInput.finish
  rw [Listing8GraphInputWrites.pointer_state mode origin l t g node rule ctx memory seed]
  rfl

theorem input_run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.run mode (Listing8GraphInputWrites.forms mode l t (values mode origin g node rule))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)=
        Listing8GraphInputWrites.finish mode origin l t g node rule memory seed := by
  rw [input_state mode origin l t g node rule ctx memory seed,Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
  exact StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (Listing8GlobalInput.trace mode l t _ ctx.resources (owners mode origin l t g node rule ctx) ctx.copies
      ctx.body.state.head.input (Listing8GraphPointerWrites.helperBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)))

theorem direction_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l)
        (Listing8GraphInputWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphInputWrites.finish mode origin l t g node rule memory seed) :=
  Listing8DirectionWrites.owned mode origin _ (Listing8DirectionGeometry.region mode l)
    (region_bounds mode origin l t g node rule ctx) ctx.body.state.head.capacity _
    (Listing8GraphInputWrites.endpoint mode origin l t g node rule ctx memory seed)

theorem body_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  rw [forms,StringWrites.owned_run_append,input_run mode origin l t g node rule ctx memory seed]
  exact ⟨Listing8GraphInputWrites.body_owned mode origin l t g node rule ctx memory seed,
    direction_owned mode origin l t g node rule ctx memory seed⟩

/-- The original emitted graph and actual bootstrap now execute through
input and direction selection with every 108/135 body store in code. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have boot:=Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  have actual:=StringDwordWritesBridge.trace mode (Listing8GlobalDirection.trace mode l t _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body.state.head
    (tailBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
  unfold Listing8GlobalDirection.program Listing8GlobalDirection.finish at actual
  rw [List.map_append] at actual
  rw [←input_state mode origin l t g node rule ctx memory seed] at actual
  change StringStack.Trace mode
    (initial mode l (values mode origin g node rule) (Listing8GraphCopyWrites.copyBacking mode origin l t g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
    (forms mode origin l t g node rule memory seed) (finish mode origin l t g node rule memory seed) at actual
  rw [←Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed] at actual
  exact ⟨StringStack.trace_append mode boot actual,body_owned mode origin l t g node rule ctx memory seed⟩

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (program mode origin l t g node rule memory seed).length=if mode=.x86 then 116 else 148 := by
  rw [program,List.length_append,forms,List.length_append,Listing8GraphInputWrites.forms,List.length_map,
    List.length_map,Listing4EntryLayout.instruction_count,Listing8GlobalInput.instruction_count,Listing8DirectionTrace.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc=
      Arithmetic.encodeNat mode (Listing8DirectionLayout.selectionEnd mode (Listing8DirectionGeometry.region mode l)) :=
  Listing8DirectionTrace.endpoint mode _ ctx.body.state.head.capacity _
    (Listing8GraphInputWrites.endpoint mode origin l t g node rule ctx memory seed)

end SmcTuring.Appendix.Listing8GraphDirectionWrites

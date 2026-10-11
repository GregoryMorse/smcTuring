module
public import SmcTuring.Appendix.Listing8GraphCopiedWriteBounds
public import SmcTuring.Appendix.Listing8InitializerWrites
public import SmcTuring.Appendix.Listing8GraphCopyWrites

public section
namespace SmcTuring.Appendix.Listing8GraphCopiedWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def forms (mode : Mode) (l : Layout) (v : Values mode) :=
  (Listing8CopiedOwners.program mode l v).map (StringStoreWrites.liftDword mode)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  Listing4EntryLayout.forms mode origin++forms mode l (values mode origin g node rule)
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8OwnerSequence.finish mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))
    (Listing8Initializer.finish mode l (values mode origin g node rule) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed))

/-- Every source/copy/target field and every later current packet is derived
from the graph context and actual initializer effect. -/
theorem initialized (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode l (values mode origin g node rule)) (initial mode l (values mode origin g node rule) backing seed) := by
  have b:=owners mode origin l t g node rule ctx
  have first:=Listing8InitializerWrites.owned mode origin _ l (values mode origin g node rule) ctx.resources
    (Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx)
    (Listing8GraphFieldWriteBounds.input mode origin l t g node rule ctx) ctx.fields.tapeReach backing seed
  have last:=Listing8OwnerSequenceWrites.owned mode origin _ (Listing8OwnerImage.owners mode l (values mode origin g node rule))
    (Listing8Prototypes.backEntry mode (nodeParams mode l).destination) (Listing8CopiedOwners.chain mode l _)
    (Listing8CopiedOwners.valid mode l _ ctx.resources b) (Listing8CopiedOwners.outside mode l _ ctx.resources b)
    (Listing8GraphCopiedWriteBounds.placement mode origin l t g node rule ctx)
    (Listing8OwnerImage.state mode l _ backing seed) (Listing8OwnerImage.entry mode l _ ctx.resources b.tapeReach backing seed)
    (Listing8OwnerImage.initial_current mode l _ ctx.resources b.tapeReach backing seed)
  have firstRun:=StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode (Listing8Initializer.trace mode l (values mode origin g node rule) ctx.resources backing seed))
  rw [forms,Listing8CopiedOwners.program,List.map_append,StringWrites.owned_run_append,firstRun]
  exact ⟨first,last⟩

theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode l (values mode origin g node rule)) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
  exact initialized mode origin l t g node rule ctx _ _

/-- One original initialization executes the real bootstrap, both transfers,
four retarget stores, tape owner and all seven copied declarations. Every
reached body store is code-owned; no future state or ownership is supplied. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l g node rule) (finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode l (values mode origin g node rule)) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have boot:=Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  have actual:=StringDwordWritesBridge.trace mode (Listing8CopiedOwners.trace mode l _ ctx.resources (owners mode origin l t g node rule ctx)
    (Listing8GraphCopyWrites.copyBacking mode origin l t g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
  change StringStack.Trace mode
    (initial mode l (values mode origin g node rule) (Listing8GraphCopyWrites.copyBacking mode origin l t g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
    (forms mode l (values mode origin g node rule))
    (Listing8OwnerSequence.finish mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))
      (Listing8Initializer.finish mode l (values mode origin g node rule)
        (initial mode l (values mode origin g node rule) (Listing8GraphCopyWrites.copyBacking mode origin l t g memory) (Listing8GlobalBoot.bodySeed mode origin seed)))) at actual
  rw [←Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed] at actual
  exact ⟨StringStack.trace_append mode boot actual,owned mode origin l t g node rule ctx memory seed⟩

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (program mode origin l g node rule).length=if mode=.x86 then 77 else 84 := by
  rw [program,List.length_append,forms,List.length_map,Listing4EntryLayout.instruction_count,Listing8CopiedOwners.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode (codeEnd mode l) := by
  unfold finish
  rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
  exact (Listing8CopiedOwners.result mode l _ ctx.resources (owners mode origin l t g node rule ctx) _ _).1

end SmcTuring.Appendix.Listing8GraphCopiedWrites

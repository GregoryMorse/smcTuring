module
public import SmcTuring.Appendix.Listing8GraphPointerWriteBounds
public import SmcTuring.Appendix.Listing8GraphCopiedWrites
public import SmcTuring.Native.StringSequenceWrites

public section
namespace SmcTuring.Appendix.Listing8GraphPointerWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def forms (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :=
  (Listing8PointerImage.program mode l t v).map (StringStoreWrites.liftDword mode)
@[expose] def program (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :=
  Listing4EntryLayout.forms mode origin++forms mode l t (values mode origin g node rule)
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8PointerCopies.finish mode l t (Listing8GraphCopiedWrites.finish mode origin l t g node rule memory seed)
@[expose] def helperBacking (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l
    (Listing8FailureGlobalImage.backing mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
      (extra mode origin l g memory)))

theorem pointer_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (codeEnd mode l)) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode)) state := by
  have fields:=Listing8GraphPointerWriteBounds.word mode origin l t g node rule ctx
  have first:=StringCopyWrites.word mode origin _ (Listing8PointerCopies.word mode l) ctx.copies.wordValid state entry fields.1 fields.2
  have next : (StringDwordCopy.wordFinish mode (Listing8PointerCopies.word mode l) state).principal.pc=
      Arithmetic.encodeNat mode (Listing8PointerCopies.dwordStart mode l) := by
    change (ConversionEffects.finish mode (Listing8PointerCopies.word mode l) state.principal).pc=_
    rw [ConversionEffects.effect mode (Listing8PointerCopies.word mode l) ctx.copies.wordValid state.principal entry]
    rfl
  have last:=StringSequenceWrites.owned mode origin _ (Listing8PointerCopies.layouts mode l t) _ (Listing8PointerCopies.chain mode l t)
    ctx.copies.dwordValid (Listing8GraphPointerWriteBounds.dwords mode origin l t g node rule ctx) _ next
  rw [Listing8PointerCopies.program,List.map_append,StringWrites.owned_run_append,StringSequenceWrites.word_run]
  exact ⟨first,last⟩

theorem copied_run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.run mode (Listing8GraphCopiedWrites.forms mode l (values mode origin g node rule))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)=Listing8GraphCopiedWrites.finish mode origin l t g node rule memory seed := by
  unfold Listing8GraphCopiedWrites.finish
  rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
  exact StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (Listing8CopiedOwners.trace mode l _ ctx.resources (owners mode origin l t g node rule ctx) _ _))

/-- All actual stores from both transfers through the complete pointer-copy
prefix lie inside the emitted graph code, including all temporary writes. -/
theorem body_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode l t (values mode origin g node rule)) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have first:=Listing8GraphCopiedWrites.owned mode origin l t g node rule ctx memory seed
  have last:=pointer_owned mode origin l t g node rule ctx (Listing8GraphCopiedWrites.finish mode origin l t g node rule memory seed)
    (Listing8GraphCopiedWrites.endpoint mode origin l t g node rule ctx memory seed)
  rw [forms,Listing8PointerImage.program,List.map_append,StringWrites.owned_run_append]
  change StringWrites.OwnedRun mode origin _ (Listing8GraphCopiedWrites.forms mode l (values mode origin g node rule)) _ ∧ _
  have executed:=copied_run mode origin l t g node rule ctx memory seed
  change StringWrites.run mode ((Listing8CopiedOwners.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
    (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)=_ at executed
  rw [executed]
  exact ⟨first,last⟩

/-- One original emitted initialization and actual bootstrap execute through
all copied owners and pointer copies to the literal input entry. Native
values, future helper bytes, PCs, traces and ownership are derived. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (program mode origin l t g node rule) (finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (forms mode l t (values mode origin g node rule)) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have boot:=Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  have actual:=StringDwordWritesBridge.trace mode (Listing8PointerImage.trace mode l t _ ctx.resources (owners mode origin l t g node rule ctx)
    ctx.copies ctx.body.state.head.input.joined (helperBacking mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
  change StringStack.Trace mode
    (initial mode l (values mode origin g node rule) (Listing8GraphCopyWrites.copyBacking mode origin l t g memory) (Listing8GlobalBoot.bodySeed mode origin seed))
    (forms mode l t (values mode origin g node rule))
    (Listing8PointerCopies.finish mode l t
      (Listing8OwnerSequence.finish mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))
        (Listing8Initializer.finish mode l (values mode origin g node rule)
          (initial mode l (values mode origin g node rule) (Listing8GraphCopyWrites.copyBacking mode origin l t g memory) (Listing8GlobalBoot.bodySeed mode origin seed))))) at actual
  rw [←Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed] at actual
  exact ⟨StringStack.trace_append mode boot actual,body_owned mode origin l t g node rule ctx memory seed⟩

theorem instruction_count (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    (program mode origin l t g node rule).length=if mode=.x86 then 89 else 105 := by
  rw [program,List.length_append,forms,List.length_map,Listing4EntryLayout.instruction_count,Listing8PointerImage.instruction_count]
  cases mode <;> rfl

theorem endpoint (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode l.input.start := by
  rw [finish,Listing8PointerCopies.endpoint mode l t ctx.copies _ (Listing8GraphCopiedWrites.endpoint mode origin l t g node rule ctx memory seed),
    ctx.body.state.head.input.joined]

end SmcTuring.Appendix.Listing8GraphPointerWrites

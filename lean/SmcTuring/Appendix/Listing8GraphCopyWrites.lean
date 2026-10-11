module
public import SmcTuring.Appendix.Listing8GraphCopyWriteBounds
public import SmcTuring.Appendix.Listing8CopyWrites

public section
namespace SmcTuring.Appendix.Listing8GraphCopyWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def bootSeed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GlobalBoot.bootSeed mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory)) seed
@[expose] def afterBoot (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing4Entry.finish mode origin (bootSeed mode origin l t g node rule memory seed)
@[expose] def copyBacking (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8PointerImage.backing mode l t (Listing8DirectionImage.backing mode l (Listing8StateImage.backing mode l
    (Listing8FailureGlobalImage.backing mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
      (extra mode origin l g memory))))
@[expose] def copyForms (mode : Mode) (l : Layout) :=
  (Listing8CopyTrace.program mode l).map (StringWrites.liftString mode)
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8CopyTrace.both mode l (afterBoot mode origin l t g node rule memory seed)

/-- The executed bootstrap equals the original copy image with its actual
register seed. This equality follows from operand restoration and overlays. -/
theorem body_entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    afterBoot mode origin l t g node rule memory seed=
      initial mode l (values mode origin g node rule) (copyBacking mode origin l t g memory) (Listing8GlobalBoot.bodySeed mode origin seed) :=
  Listing8GlobalBoot.body_entry mode origin l t _ _ ctx.resources ctx.boot ctx.body _ seed

/-- Both actual ordered copies start at the computed bootstrap result.
The graph context derives every code bound and all future readiness. -/
theorem copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (afterBoot mode origin l t g node rule memory seed) (copyForms mode l)
      (finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) (copyForms mode l)
      (afterBoot mode origin l t g node rule memory seed) := by
  unfold finish
  rw [body_entry mode origin l t g node rule ctx memory seed]
  exact Listing8CopyWrites.copies mode origin _ l _ ctx.resources
    (Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx) _ _

/-- One emitted original initialization and actual bootstrap execute into
both ordered copies. No host memory or PC reset bridges the stages. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (Listing4EntryLayout.forms mode origin++copyForms mode l) (finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) (copyForms mode l)
      (afterBoot mode origin l t g node rule memory seed) := by
  have first:=Listing4Entry.trace mode origin (bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  have last:=copies mode origin l t g node rule ctx memory seed
  exact ⟨StringStack.trace_append mode first last.1,last.2⟩

end SmcTuring.Appendix.Listing8GraphCopyWrites

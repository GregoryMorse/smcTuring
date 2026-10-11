module
public import SmcTuring.Appendix.Listing8GraphJumpWrites
public import SmcTuring.Appendix.Listing4TargetWrites

public section
namespace SmcTuring.Appendix.Listing8GraphEntryWrites
set_option maxHeartbeats 1000000
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

theorem boot_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing4EntryLayout.forms mode origin) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  Listing4TargetWrites.entry_owned mode origin _ origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
    ⟨Nat.le_refl _,Listing8GraphJumpWrites.stack_inside mode origin l t g node rule ctx⟩

theorem boot_run (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.run mode (Listing4EntryLayout.forms mode origin) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)=
      Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed :=
  StringWrites.trace_run_eq mode (Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))

set_option maxHeartbeats 4000000 in
theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  unfold Listing8GraphJumpWrites.program
  exact StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    (Listing4EntryLayout.forms mode origin) (Listing8GraphJumpWrites.forms mode origin l t g node rule memory seed)
    (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)
    (Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body))
    (boot_owned mode origin l t g node rule ctx memory seed) (Listing8GraphJumpWrites.body_owned mode origin l t g node rule ctx memory seed)

/-- Every instruction of the original bootstrap and complete first body/CALL
has a nonempty architectural store whose entire byte span lies in emitted code. -/
theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
      (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed) (Listing8GraphJumpWrites.finish mode origin l t g node rule memory seed) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed) (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) :=
  ⟨Listing8GraphJumpWrites.trace mode origin l t g node rule ctx memory seed,owned mode origin l t g node rule ctx memory seed⟩

end SmcTuring.Appendix.Listing8GraphEntryWrites

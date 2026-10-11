module
public import SmcTuring.Appendix.Listing8GraphNextCallImage

public section
namespace SmcTuring.Appendix.Listing8GraphNextEarlyPrefix
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤l.start) :
    ByteMemory.bytesAt (Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  have destinations:=destinations mode (nextLayout mode origin l g node rule target)
  have lower : l.start≤(nodeParams mode (nextLayout mode origin l g node rule target)).destination:=destinations.1
  rw [Listing8GraphNextCopies.effect mode origin l t g node rule target ctx selected memory seed,
    byte_frame _ _ _ _ _ (Or.inr (by omega)),byte_frame _ _ _ _ _ (Or.inr (by omega))]

theorem owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤l.start) :
    ByteMemory.bytesAt (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  have patch:=Listing8EarlyOwners.patch_after mode l
  have input:=Listing8EarlyOwners.input_after mode l ctx.resources
  have source:=Listing8OwnerImage.source_field_bounds mode l
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  have endInput : l.input.start≤Listing8LiteralInput.endPC mode l.input := by
    have coords:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have direction:=ctx.fields.directionAfter
  rw [Listing8GraphNextOwnerFrames.live_frame mode origin l t g node rule target ctx selected memory seed observed count
    (fun site member => Or.inr (by
      have located:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member).1
      change patchStart mode l+40≤site.owner at located;omega))
    (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))]
  exact copies mode origin l t g node rule target ctx selected memory seed observed count before

theorem pointers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (observed count : Nat) (before : observed+count≤l.start) :
    ByteMemory.bytesAt (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory observed count=
      ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory observed count := by
  have lower:=Listing8EarlyGeometry.second_cursor mode l
  change l.start≤(Listing8PointerCopies.word mode l).destination at lower
  change ByteMemory.bytesAt (Listing8PointerCopies.finish mode l t (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed)).principal.memory observed count=_
  rw [Listing8PointerCopies.window_frame mode l t ctx.copies _
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1 observed count
    (Or.inr (by omega)) (fun writer member => Or.inr (Nat.le_trans before (Listing8EarlyGeometry.pointer_targets mode l t ctx.copies writer member)))]
  exact owners mode origin l t g node rule target ctx selected memory seed observed count before

end SmcTuring.Appendix.Listing8GraphNextEarlyPrefix

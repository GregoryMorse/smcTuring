module
public import SmcTuring.Appendix.Listing8GraphEntryReads

public section
namespace SmcTuring.Appendix.Listing8GraphReturnReads
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (nonhalt : ¬Listing8GraphRun.Halted g node rule) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphReturnWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  exact StringReadSuffix.contained mode origin _ _ _ _
    (Listing8GraphEntryReads.contained mode origin l t g node rule ctx memory seed)
    (Listing8TerminalReadClasses.target mode origin (Listing8BootImage.beginPC mode origin))
    (Listing8GraphReturnWrites.owned mode origin l t g node rule ctx memory seed nonhalt)

theorem halted (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphHaltReturnWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  exact StringReadSuffix.contained mode origin _ _ _ _
    (Listing8GraphEntryReads.contained mode origin l t g node rule ctx memory seed)
    (Listing8TerminalReadClasses.target mode origin (Listing8JumpLayout.failPC mode origin))
    (Listing8GraphHaltReturnWrites.owned mode origin l t g node rule ctx memory seed halted)

end SmcTuring.Appendix.Listing8GraphReturnReads

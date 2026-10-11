module
public import SmcTuring.Appendix.Listing8GraphReturnReads

public section
namespace SmcTuring.Appendix.Listing8GraphHaltTerminalReads
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

@[expose] def tailForms (mode : Mode) (origin : Nat) (l : Layout) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) :=
  Listing8GraphHaltTerminalWrites.tableForms mode origin g++
    Listing8GraphHaltTerminalWrites.resetForms mode origin l g++
    Listing8GraphHaltTerminalWrites.nodeForms mode origin g node rule

theorem program_split (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphHaltTerminalWrites.program mode origin l t g node rule memory seed=
      Listing8GraphHaltReturnWrites.program mode origin l t g node rule memory seed++tailForms mode origin l g node rule := by
  simp only [Listing8GraphHaltTerminalWrites.program,tailForms,List.append_assoc]

theorem tail_local (mode : Mode) (origin : Nat) (l : Layout) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) :
    ∀ form∈tailForms mode origin l g node rule,StringReadWindows.Local mode form := by
  simp only [tailForms,List.mem_append]
  intro form member
  rcases member with (table | reset) | nodes
  · exact Listing8TerminalReadClasses.transitions mode _ _ form table
  · exact Listing8TerminalReadClasses.reset mode _ form reset
  · exact Listing8TerminalReadClasses.nodes mode _ _ form nodes

/-- All reads on the immediate original halt path, including the two
original copies and every trailing declaration, follow one initialization. -/
theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (halted : Listing8GraphRun.Halted g node rule) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphHaltTerminalWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  have owned:=Listing8GraphHaltTerminalWrites.owned mode origin l t g node rule ctx memory seed halted
  rw [program_split] at owned ⊢
  exact StringReadSuffix.contained mode origin _ _ _ _
    (Listing8GraphReturnReads.halted mode origin l t g node rule ctx memory seed halted)
    (tail_local mode origin l g node rule) owned

end SmcTuring.Appendix.Listing8GraphHaltTerminalReads

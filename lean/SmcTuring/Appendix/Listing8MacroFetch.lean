module
public import SmcTuring.Native.StringFetchPermissions
public import SmcTuring.Native.StringMacroTrace
public import SmcTuring.Appendix.Listing8MacroPCWindows
public import SmcTuring.Appendix.Listing8MacroReads

public section
namespace SmcTuring.Appendix.Listing8MacroFetch
open Native StringMacroLayout
abbrev Placement:=Listing8MacroWriteBounds.Placement

theorem actual (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state) :
    StringStack.Trace mode state
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode))
      (StringMacroEffects.finish mode p state) :=
  StringFetchWindows.lift_string_trace mode (StringMacroTrace.trace mode p state ready)

/-- Every actual TRANSFERDATA classifier/fetch window follows initial
readiness and static original placement, including short MOVS headers. -/
theorem contained (mode : Mode) (start stop : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode start stop p)
    (capacity : stop<2^(8*mode.wordBytes)) :
    StringFetchWindows.Run mode ⟨start,stop⟩
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state :=
  StringFetchWindows.of_pc_run mode ⟨start,stop⟩ (actual mode p state ready)
    (Listing8MacroPCWindows.contained mode start stop p state ready placed capacity)

theorem complete (mode : Mode) (start stop : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode start stop p)
    (capacity : stop<2^(8*mode.wordBytes)) :
    StringStack.Trace mode state
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode))
      (StringMacroEffects.finish mode p state) ∧
    StringFetchWindows.Run mode ⟨start,stop⟩
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state ∧
    StringWrites.OwnedRun mode start stop
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state ∧
    StringReadRuns.Run mode ⟨start,stop⟩
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state :=
  ⟨actual mode p state ready,contained mode start stop p state ready placed capacity,
    Listing8MacroWrites.owned mode start stop p state ready placed,Listing8MacroReads.contained mode start stop p state ready placed⟩

theorem next_access (mode : Mode) (environment : MappedExecution.Environment) (start stop : Nat)
    (mapping : MappedExecution.Mapped mode environment ⟨start,stop⟩)
    (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state)
    (placed : Placement mode start stop p) (capacity : stop<2^(8*mode.wordBytes))
    (before : List (StringStack.Form mode)) (form : StringStack.Form mode) (after : List (StringStack.Form mode))
    (cut : before++form::after=(StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      StringFetchWindows.Within mode ⟨start,stop⟩ reached ∧ StringFetchPermissions.Allowed mode environment reached ∧
      StringWrites.CodeWrite mode start stop form reached ∧
      MappedExecution.Window mode environment .write (StringWrites.packet mode form reached).address (StringWrites.packet mode form reached).bytes.length ∧
      StringReadWindows.Within mode ⟨start,stop⟩ form reached ∧ StringReadPermissions.Allowed mode environment form reached ∧
      StringStack.Trace mode (StringStack.execute mode form reached) after (StringMacroEffects.finish mode p state) := by
  have facts:=complete mode start stop p state ready placed capacity
  exact StringFetchPermissions.next_access mode environment start stop mapping facts.1 facts.2.1 facts.2.2.1 facts.2.2.2 before form after cut

end SmcTuring.Appendix.Listing8MacroFetch

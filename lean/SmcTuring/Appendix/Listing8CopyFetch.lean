module
public import SmcTuring.Appendix.Listing8MacroFetch
public import SmcTuring.Appendix.Listing8CopyReads

public section
namespace SmcTuring.Appendix.Listing8CopyFetch
open Native Listing8CopyImage
abbrev Placement:=Listing8CopyWriteBounds.Placement

theorem original (mode : Mode) (start stop : Nat) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (placed : Placement mode start stop l) (capacity : stop<2^(8*mode.wordBytes))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringFetchWindows.Run mode ⟨start,stop⟩ ((Listing8CopyTrace.program mode l).map (StringWrites.liftString mode))
      (initial mode l v backing seed) := by
  have first:=Listing8MacroFetch.contained mode start stop (nodeParams mode l) (initial mode l v backing seed)
    (Listing8CopyTrace.first_ready mode l v resources backing seed) (Listing8CopyWriteBounds.node mode start stop l placed) capacity
  have second:=Listing8MacroFetch.contained mode start stop (transitionParams mode l)
    (Listing8CopyTrace.first mode l (initial mode l v backing seed))
    (Listing8CopyTrace.second_ready mode l v resources backing seed) (Listing8CopyWriteBounds.transition mode start stop l placed) capacity
  rw [Listing8CopyTrace.program,List.map_append,StringFetchWindows.append,StringWrites.run_lift_string,StringMacroEffects.program_run]
  exact ⟨first,second⟩

/-- Both live ordered copies include every decoder request. The second
ready state is derived from the first actual transfer; no image is reset. -/
theorem live (mode : Mode) (start stop : Nat) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (placed : Placement mode start stop l) (capacity : stop<2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringFetchWindows.Run mode ⟨start,stop⟩ ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have ready:=Listing8LiveCopies.first_ready mode l resources state entry forward
    (Listing8MainCopyImage.node_current mode l v _ current)
  have next:=Listing8LiveCopies.second_ready mode l resources state ready
    (Listing8MainCopyImage.rule_current mode l v _ current)
  have first:=Listing8MacroFetch.contained mode start stop (nodeParams mode l) state ready
    (Listing8CopyWriteBounds.node mode start stop l placed) capacity
  have second:=Listing8MacroFetch.contained mode start stop (transitionParams mode l) (Listing8CopyTrace.first mode l state) next
    (Listing8CopyWriteBounds.transition mode start stop l placed) capacity
  change StringFetchWindows.Run mode ⟨start,stop⟩
    (((StringProgram.forms mode l.start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size)++
      (StringProgram.forms mode (secondStart mode l) (transitionParams mode l).source (transitionParams mode l).destination (transitionParams mode l).size)).map
      (StringWrites.liftString mode)) state
  rw [List.map_append,StringFetchWindows.append,StringWrites.run_lift_string]
  have completed : StringExecution.run mode
      (StringProgram.forms mode l.start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size) state=
      Listing8CopyTrace.first mode l state := StringMacroEffects.program_run mode (nodeParams mode l) state
  rw [completed]
  exact ⟨first,second⟩

theorem complete_original (mode : Mode) (start stop : Nat) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (placed : Placement mode start stop l) (capacity : stop<2^(8*mode.wordBytes))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.Trace mode (initial mode l v backing seed) ((Listing8CopyTrace.program mode l).map (StringWrites.liftString mode))
      (Listing8CopyTrace.both mode l (initial mode l v backing seed)) ∧
    StringFetchWindows.Run mode ⟨start,stop⟩ ((Listing8CopyTrace.program mode l).map (StringWrites.liftString mode)) (initial mode l v backing seed) ∧
    StringWrites.OwnedRun mode start stop ((Listing8CopyTrace.program mode l).map (StringWrites.liftString mode)) (initial mode l v backing seed) ∧
    StringReadRuns.Run mode ⟨start,stop⟩ ((Listing8CopyTrace.program mode l).map (StringWrites.liftString mode)) (initial mode l v backing seed) := by
  have actual:=Listing8CopyWrites.copies mode start stop l v resources placed backing seed
  exact ⟨actual.1,original mode start stop l v resources placed capacity backing seed,actual.2,
    Listing8CopyReads.original mode start stop l v resources placed backing seed⟩

theorem complete_live (mode : Mode) (start stop : Nat) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (placed : Placement mode start stop l) (capacity : stop<2^(8*mode.wordBytes))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringStack.Trace mode state ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) (Listing8MainCopies.finish mode l state) ∧
    StringFetchWindows.Run mode ⟨start,stop⟩ ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state ∧
    StringWrites.OwnedRun mode start stop ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state ∧
    StringReadRuns.Run mode ⟨start,stop⟩ ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have actual:=Listing8MainCopyWrites.execute mode start stop l v resources placed state entry forward current
  exact ⟨actual.1,live mode start stop l v resources placed capacity state entry forward current,actual.2,
    Listing8CopyReads.live mode start stop l v resources placed state entry forward current⟩

theorem next_live_access (mode : Mode) (environment : MappedExecution.Environment) (start stop : Nat)
    (mapping : MappedExecution.Mapped mode environment ⟨start,stop⟩)
    (l : Layout) (v : Values mode) (resources : Resources mode l) (placed : Placement mode start stop l)
    (capacity : stop<2^(8*mode.wordBytes)) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l v state.principal.memory)
    (before : List (StringStack.Form mode)) (form : StringStack.Form mode) (after : List (StringStack.Form mode))
    (cut : before++form::after=(Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      StringFetchWindows.Within mode ⟨start,stop⟩ reached ∧ StringFetchPermissions.Allowed mode environment reached ∧
      StringWrites.CodeWrite mode start stop form reached ∧
      MappedExecution.Window mode environment .write (StringWrites.packet mode form reached).address (StringWrites.packet mode form reached).bytes.length ∧
      StringReadWindows.Within mode ⟨start,stop⟩ form reached ∧ StringReadPermissions.Allowed mode environment form reached ∧
      StringStack.Trace mode (StringStack.execute mode form reached) after (Listing8MainCopies.finish mode l state) := by
  have facts:=complete_live mode start stop l v resources placed capacity state entry forward current
  exact StringFetchPermissions.next_access mode environment start stop mapping facts.1 facts.2.1 facts.2.2.1 facts.2.2.2 before form after cut

end SmcTuring.Appendix.Listing8CopyFetch

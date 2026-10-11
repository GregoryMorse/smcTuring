module
public import SmcTuring.Appendix.Listing8MacroReads
public import SmcTuring.Appendix.Listing8MainCopyWrites

public section
namespace SmcTuring.Appendix.Listing8CopyReads
open Native Listing8CopyImage
abbrev Placement:=Listing8CopyWriteBounds.Placement

/-- Both original copies include every SI-source read. The second entry
and source image follow from the first actual transfer, without a later
read/ready/trace premise. -/
theorem original (mode : Mode) (start stop : Nat) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (placed : Placement mode start stop l) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringReadRuns.Run mode ⟨start,stop⟩ ((Listing8CopyTrace.program mode l).map (StringWrites.liftString mode))
      (initial mode l v backing seed) := by
  have first:=Listing8MacroReads.contained mode start stop (nodeParams mode l) (initial mode l v backing seed)
    (Listing8CopyTrace.first_ready mode l v resources backing seed) (Listing8CopyWriteBounds.node mode start stop l placed)
  have second:=Listing8MacroReads.contained mode start stop (transitionParams mode l)
    (Listing8CopyTrace.first mode l (initial mode l v backing seed))
    (Listing8CopyTrace.second_ready mode l v resources backing seed) (Listing8CopyWriteBounds.transition mode start stop l placed)
  rw [Listing8CopyTrace.program,List.map_append,StringReadRuns.append,StringWrites.run_lift_string,StringMacroEffects.program_run]
  exact ⟨first,second⟩

/-- The repeated body's current maintained source packets derive the
same two complete read certificates; memory is never reinitialized. -/
theorem live (mode : Mode) (start stop : Nat) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (placed : Placement mode start stop l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringReadRuns.Run mode ⟨start,stop⟩ ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode)) state := by
  have ready:=Listing8LiveCopies.first_ready mode l resources state entry forward
    (Listing8MainCopyImage.node_current mode l v _ current)
  have next:=Listing8LiveCopies.second_ready mode l resources state ready
    (Listing8MainCopyImage.rule_current mode l v _ current)
  have first:=Listing8MacroReads.contained mode start stop (nodeParams mode l) state ready
    (Listing8CopyWriteBounds.node mode start stop l placed)
  have second:=Listing8MacroReads.contained mode start stop (transitionParams mode l) (Listing8CopyTrace.first mode l state) next
    (Listing8CopyWriteBounds.transition mode start stop l placed)
  change StringReadRuns.Run mode ⟨start,stop⟩
    (((StringProgram.forms mode l.start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size)++
      (StringProgram.forms mode (secondStart mode l) (transitionParams mode l).source (transitionParams mode l).destination (transitionParams mode l).size)).map
      (StringWrites.liftString mode)) state
  rw [List.map_append,StringReadRuns.append,StringWrites.run_lift_string]
  have completed : StringExecution.run mode
      (StringProgram.forms mode l.start (nodeParams mode l).source (nodeParams mode l).destination (nodeParams mode l).size) state=
      Listing8CopyTrace.first mode l state := StringMacroEffects.program_run mode (nodeParams mode l) state
  rw [completed]
  exact ⟨first,second⟩

end SmcTuring.Appendix.Listing8CopyReads

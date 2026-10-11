module
public import SmcTuring.Appendix.Listing8LoopControlWrites
public import SmcTuring.Native.StringSequentialPackets

public section
namespace SmcTuring.Appendix.Listing8SequentialTails
open Native

theorem direction (mode : Mode) (l : Listing8DirectionLayout.Layout) (state : StringExecution.State mode) :
    ∀ form∈(Listing8DirectionTrace.program mode l state).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8DirectionTrace.program,List.map_append,List.mem_append]
  intro form member
  rcases member with helpers | packets
  · exact StringSequentialFamilies.sequence mode _ form helpers
  · exact StringSequentialPackets.packets mode _ _ form packets

theorem head (mode : Mode) (l : Listing8DirectionLayout.Layout) (state : StringExecution.State mode) :
    ∀ form∈(Listing8HeadTailTrace.program mode l state).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8HeadTailTrace.program,List.map_append,List.mem_append]
  intro form member
  rcases member with (xors | masks) | heads
  · exact StringSequentialPackets.xors mode _ form xors
  · exact StringSequentialPackets.packets mode _ _ form masks
  · exact StringSequentialPackets.packets mode _ _ form heads

theorem state (mode : Mode) (l : Listing8StateLayout.Layout) (current : StringExecution.State mode) :
    ∀ form∈(Listing8StateTrace.program mode l current).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8StateTrace.program,List.map_append,List.mem_append]
  intro form member
  rcases member with helpers | packets
  · exact StringSequentialFamilies.sequence mode _ form helpers
  · exact StringSequentialPackets.packets mode _ _ form packets

theorem failure (mode : Mode) (l : Listing8FailureLayout.Layout) (state : StringExecution.State mode) :
    ∀ form∈(Listing8FailureTrace.program mode l state).map StringStack.Form.previous,StringPCSteps.Sequential mode form := by
  simp only [Listing8FailureTrace.program,List.map_append,List.map_cons,List.map_nil,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  intro form member
  rcases member with ((rfl | owner) | comparison) | post
  · exact StringSequentialPackets.arithmetic mode _
  · have mapped : (Listing8FailureTrace.ownerProgram mode l).map StringStack.Form.previous=
        (StringInit.forms mode (Listing8FailureLayout.ownerPC l) l.sentinel).map (StringWrites.liftString mode) := by
      rw [Listing8FailureTrace.ownerProgram,List.map_map];rfl
    rw [mapped] at owner
    exact StringSequentialPackets.initializers mode _ _ form owner
  · exact StringSequentialPackets.controls mode _ form comparison
  · have mapped : ((DwordPackets.program mode (Listing8FailureLayout.post mode l)
        (Listing8FailureImage.comparisonFinish mode l state).principal).map StringControl.Form.previous).map StringStack.Form.previous=
        (DwordPackets.program mode (Listing8FailureLayout.post mode l)
          (Listing8FailureImage.comparisonFinish mode l state).principal).map (StringStoreWrites.liftDword mode) := by rw [List.map_map];rfl
    rw [mapped] at post
    exact StringSequentialPackets.packets mode _ _ form post

end SmcTuring.Appendix.Listing8SequentialTails

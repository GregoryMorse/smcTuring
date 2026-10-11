module
public import SmcTuring.Appendix.Listing8LoopControlWrites
public import SmcTuring.Native.StringPacketReadClasses

public section
namespace SmcTuring.Appendix.Listing8TailReadClasses
open Native

theorem direction (mode : Mode) (l : Listing8DirectionLayout.Layout) (state : StringExecution.State mode) :
    ∀ form∈(Listing8DirectionTrace.program mode l state).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  simp only [Listing8DirectionTrace.program,List.map_append,List.mem_append]
  intro form member
  rcases member with helpers | packets
  · exact StringScalarLists.sequence mode _ form helpers
  · exact StringPacketReadClasses.packets mode _ _ form packets

theorem head (mode : Mode) (l : Listing8DirectionLayout.Layout) (state : StringExecution.State mode) :
    ∀ form∈(Listing8HeadTailTrace.program mode l state).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  simp only [Listing8HeadTailTrace.program,List.map_append,List.mem_append]
  intro form member
  rcases member with (xors | masks) | heads
  · exact StringPacketReadClasses.xors mode _ form xors
  · exact StringPacketReadClasses.packets mode _ _ form masks
  · exact StringPacketReadClasses.packets mode _ _ form heads

theorem state (mode : Mode) (l : Listing8StateLayout.Layout) (current : StringExecution.State mode) :
    ∀ form∈(Listing8StateTrace.program mode l current).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  simp only [Listing8StateTrace.program,List.map_append,List.mem_append]
  intro form member
  rcases member with helpers | packets
  · exact StringScalarLists.sequence mode _ form helpers
  · exact StringPacketReadClasses.packets mode _ _ form packets

theorem failure (mode : Mode) (l : Listing8FailureLayout.Layout) (state : StringExecution.State mode) :
    ∀ form∈(Listing8FailureTrace.program mode l state).map StringStack.Form.previous,StringReadWindows.Local mode form := by
  simp only [Listing8FailureTrace.program,List.map_append,List.map_cons,List.map_nil,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  intro form member
  rcases member with ((rfl | owner) | comparison) | post
  · exact StringPacketReadClasses.arithmetic mode _
  · have mapped : (Listing8FailureTrace.ownerProgram mode l).map StringStack.Form.previous=
        (StringInit.forms mode (Listing8FailureLayout.ownerPC l) l.sentinel).map (StringWrites.liftString mode) := by
      rw [Listing8FailureTrace.ownerProgram,List.map_map];rfl
    rw [mapped] at owner
    exact StringPacketReadClasses.initializers mode _ _ form owner
  · exact StringPacketReadClasses.controls mode _ form comparison
  · have mapped : ((DwordPackets.program mode (Listing8FailureLayout.post mode l)
        (Listing8FailureImage.comparisonFinish mode l state).principal).map StringControl.Form.previous).map StringStack.Form.previous=
        (DwordPackets.program mode (Listing8FailureLayout.post mode l)
          (Listing8FailureImage.comparisonFinish mode l state).principal).map (StringStoreWrites.liftDword mode) := by rw [List.map_map];rfl
    rw [mapped] at post
    exact StringPacketReadClasses.packets mode _ _ form post

theorem jump_return (mode : Mode) (origin : Nat) (failed : Bool) :
    ∀ form∈Listing8JumpReturn.program mode origin failed,StringReadWindows.Local mode form := by
  cases mode <;> simp [Listing8JumpReturn.program,Listing8JumpLayout.forms,Listing8JumpLayout.prefixForms,
    Listing8JumpLayout.exchange,Listing8JumpLayout.exchangeSaved,Listing8JumpLayout.adjust,Listing8JumpLayout.call,
    Listing4TargetLayout.forms,Listing4TargetLayout.first,Listing4TargetLayout.adjust,Listing4TargetLayout.third,
    Listing4TargetLayout.fourth,Listing4TargetLayout.fifth,StackMemory.form,StackAdjust.subtract,
    WordMemoryArithmetic.form,WordMemoryArithmetic.opcode,StringOperands.subtract,StringStack.native,StringDwordCopy.native,
    StringReadWindows.Local,StringReadWindows.ControlLocal,StringReadWindows.DwordLocal,
    StringReadWindows.StringLocal,StringReadWindows.NativeLocal]

end SmcTuring.Appendix.Listing8TailReadClasses

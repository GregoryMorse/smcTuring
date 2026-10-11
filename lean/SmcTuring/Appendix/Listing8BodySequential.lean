module
public import SmcTuring.Appendix.Listing8SequentialScalars
public import SmcTuring.Appendix.Listing8SequentialTails
public import SmcTuring.Appendix.Listing8MacroPCWindows

public section
namespace SmcTuring.Appendix.Listing8BodySequential
open Native Listing8CopyImage
abbrev Targets:=Listing8PointerCopies.Targets

theorem copies (mode : Mode) (l : Layout) :
    ∀ form∈(Listing8MainCopies.program mode l).map (StringWrites.liftString mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8MainCopies.program,Listing8CopyTrace.program,List.map_append,List.mem_append]
  intro form member
  rcases member with first | second
  · rcases List.mem_map.mp first with ⟨original,inside,rfl⟩
    exact Listing8MacroPCWindows.forms_sequential mode _ _ _ _ original inside
  · rcases List.mem_map.mp second with ⟨original,inside,rfl⟩
    exact Listing8MacroPCWindows.forms_sequential mode _ _ _ _ original inside

theorem retarget (mode : Mode) (l : Layout) (v : Values mode) :
    ∀ form∈(Listing8MainRetarget.program mode l v).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8MainRetarget.program,List.map_append,List.mem_append]
  intro form member
  rcases member with copied | tail
  · have mapped : ((Listing8MainCopies.program mode l).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)=
        (Listing8MainCopies.program mode l).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
    rw [mapped] at copied
    exact copies mode l form copied
  · exact Listing8SequentialScalars.retarget mode l v form tail

theorem owners (mode : Mode) (l : Layout) (v : Values mode) :
    ∀ form∈(Listing8MainLiveOwners.program mode l v).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8MainLiveOwners.program,List.map_append,List.mem_append]
  intro form member
  rcases member with first | second
  · exact retarget mode l v form first
  · exact Listing8SequentialScalars.owners mode _ form second

theorem main_prefix (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :
    ∀ form∈(Listing8MainPrefix.program mode l t v).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8MainPrefix.program,List.map_append,List.mem_append]
  intro form member
  rcases member with first | second
  · exact owners mode l v form first
  · exact Listing8SequentialScalars.pointers mode l t form second

theorem input (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :
    ∀ form∈(Listing8MainInput.program mode l t v).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8MainInput.program,List.map_append,List.mem_append]
  intro form member
  rcases member with first | second
  · exact main_prefix mode l t v form first
  · exact StringSequentialFamilies.mixed mode _ form second

theorem direction (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :
    ∀ form∈(Listing8LoopDirection.program mode l t v state).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8LoopDirection.program,List.map_append,List.mem_append]
  intro form member
  rcases member with first | second
  · exact input mode l t v form first
  · exact Listing8SequentialTails.direction mode _ _ form second

theorem head (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (state : StringExecution.State mode) :
    ∀ form∈(Listing8LoopHead.program mode l t v state).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8LoopHead.program,List.map_append,List.mem_append]
  intro form member
  rcases member with first | second
  · exact direction mode l t v state form first
  · exact Listing8SequentialTails.head mode _ _ form second

theorem state (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (initial : StringExecution.State mode) :
    ∀ form∈(Listing8LoopState.program mode l t v initial).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8LoopState.program,List.map_append,List.mem_append]
  intro form member
  rcases member with first | second
  · exact head mode l t v initial form first
  · exact Listing8SequentialTails.state mode _ _ form second

/-- Every form in the actual pre-CALL body is sequential, including zero
CALL readers. This is proved from the original generators for all values. -/
theorem failure (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (sentinel begin : Nat)
    (initial : StringExecution.State mode) :
    ∀ form∈(Listing8LoopFailure.program mode l t v sentinel begin initial).map StringStack.Form.previous,StringPCSteps.Sequential mode form := by
  simp only [Listing8LoopFailure.program,List.map_append,List.mem_append]
  intro form member
  rcases member with first | second
  · have mapped : ((Listing8LoopState.program mode l t v initial).map StringControl.Form.previous).map StringStack.Form.previous=
        (Listing8LoopState.program mode l t v initial).map (StringStoreWrites.liftDword mode) := by rw [List.map_map];rfl
    rw [mapped] at first
    exact state mode l t v initial form first
  · exact Listing8SequentialTails.failure mode _ _ form second

end SmcTuring.Appendix.Listing8BodySequential

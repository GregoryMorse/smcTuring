module
public import SmcTuring.Appendix.Listing4EntryFetch
public import SmcTuring.Appendix.Listing8LoopControlFetch
public import SmcTuring.Appendix.Listing8GraphEntryReads

public section
namespace SmcTuring.Appendix.Listing8GraphBodySequential
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def tail (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphEntryReads.inputTail mode l t (values mode origin g node rule)++
    (Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l)
      (Listing8GraphInputWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode)++
    (Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l)
      (Listing8GraphDirectionWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode)++
    (Listing8StateTrace.program mode (Listing8StateGeometry.region mode l)
      (Listing8GraphHeadWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode)++
    (Listing8FailureTrace.program mode (Listing8GraphFailureWrites.region mode origin l g)
      (Listing8GraphStateWrites.finish mode origin l t g node rule memory seed)).map StringStack.Form.previous

theorem input_sequential (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :
    ∀ form∈Listing8GraphEntryReads.inputTail mode l t v,StringPCSteps.Sequential mode form := by
  simp only [Listing8GraphEntryReads.inputTail,List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  intro form member
  rcases member with (((retarget | rfl) | owners) | pointers) | input
  · exact StringSequentialFamilies.retargets mode _ form retarget
  · cases mode <;> trivial
  · exact Listing8SequentialScalars.owners mode _ form owners
  · exact Listing8SequentialScalars.pointers mode l t form pointers
  · exact StringSequentialFamilies.mixed mode _ form input

theorem split (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphFailureWrites.program mode origin l t g node rule memory seed=
      (Listing4EntryLayout.forms mode origin++Listing8GraphCopyWrites.copyForms mode l)++
        tail mode origin l t g node rule memory seed := by
  simp only [Listing8GraphFailureWrites.program,Listing8GraphFailureWrites.forms,
    Listing8GraphStateWrites.forms,Listing8GraphHeadWrites.forms,Listing8GraphDirectionWrites.forms,
    Listing8GraphInputWrites.forms,Listing8GlobalInput.program,Listing8PointerImage.program,
    Listing8CopiedOwners.program,Listing8Initializer.program,Listing8GraphCopyWrites.copyForms,
    tail,Listing8GraphEntryReads.inputTail,List.map_append,List.map_map,Function.comp_def,List.append_assoc]
  rfl

theorem tail_sequential (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∀ form∈tail mode origin l t g node rule memory seed,StringPCSteps.Sequential mode form := by
  simp only [tail,List.mem_append]
  intro form member
  rcases member with (((input | direction) | head) | state) | failure
  · exact input_sequential mode l t _ form input
  · exact Listing8SequentialTails.direction mode _ _ form direction
  · exact Listing8SequentialTails.head mode _ _ form head
  · exact Listing8SequentialTails.state mode _ _ form state
  · exact Listing8SequentialTails.failure mode _ _ form failure

theorem sequential (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∀ form∈Listing8GraphFailureWrites.program mode origin l t g node rule memory seed,StringPCSteps.Sequential mode form := by
  rw [split]
  simp only [List.mem_append]
  intro form member
  rcases member with (entry | copies) | later
  · exact Listing4EntryFetch.sequential mode origin form entry
  · exact Listing8BodySequential.copies mode l form copies
  · exact tail_sequential mode origin l t g node rule memory seed form later

end SmcTuring.Appendix.Listing8GraphBodySequential

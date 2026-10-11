module
public import SmcTuring.Appendix.Listing8CopyReads
public import SmcTuring.Appendix.Listing8TerminalReadClasses
public import SmcTuring.Appendix.Listing8TailReadClasses
public import SmcTuring.Native.StringReadSuffix

public section
namespace SmcTuring.Appendix.Listing8GraphEntryReads
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

@[expose] def inputTail (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :=
  (StringRetarget.program mode (Listing8ModeOffsets.sites mode (patchLayout mode l))++
    [Listing8Initializer.tapeForm mode l v]++Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l v)++
    Listing8PointerCopies.program mode l t++
    (Listing8LiteralComposition.program mode l.input v.rule v.tape v.fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)

@[expose] def scalarTail (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  inputTail mode l t (values mode origin g node rule)++
    (Listing8DirectionTrace.program mode (Listing8DirectionGeometry.region mode l)
      (Listing8GraphInputWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode)++
    (Listing8HeadTailTrace.program mode (Listing8DirectionGeometry.region mode l)
      (Listing8GraphDirectionWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode)++
    (Listing8StateTrace.program mode (Listing8StateGeometry.region mode l)
      (Listing8GraphHeadWrites.finish mode origin l t g node rule memory seed)).map (StringStoreWrites.liftDword mode)++
    (Listing8FailureTrace.program mode (Listing8GraphFailureWrites.region mode origin l g)
      (Listing8GraphStateWrites.finish mode origin l t g node rule memory seed)).map StringStack.Form.previous++
    Listing8JumpLayout.forms mode origin (Listing8GraphBackedge.failed mode origin l t g node rule memory seed)

theorem program_split (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphJumpWrites.program mode origin l t g node rule memory seed=
      (Listing4EntryLayout.forms mode origin++Listing8GraphCopyWrites.copyForms mode l)++
        scalarTail mode origin l t g node rule memory seed := by
  simp only [Listing8GraphJumpWrites.program,Listing8GraphJumpWrites.forms,Listing8GraphFailureWrites.forms,
    Listing8GraphStateWrites.forms,Listing8GraphHeadWrites.forms,Listing8GraphDirectionWrites.forms,
    Listing8GraphInputWrites.forms,Listing8GlobalInput.program,Listing8PointerImage.program,
    Listing8CopiedOwners.program,Listing8Initializer.program,Listing8GraphCopyWrites.copyForms,
    scalarTail,inputTail,List.map_append,List.map_map,Function.comp_def,List.append_assoc]
  rfl

theorem input_local (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) :
    ∀ form∈inputTail mode l t v,StringReadWindows.Local mode form := by
  simp only [inputTail,List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  intro form member
  rcases member with (((retarget | rfl) | owners) | pointers) | input
  · exact StringScalarLists.retargets mode _ form retarget
  · cases mode <;> trivial
  · exact Listing8ScalarReadClasses.owners mode _ form owners
  · exact Listing8ScalarReadClasses.pointers mode l t form pointers
  · exact StringScalarLists.mixed mode _ form input

theorem tail_local (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ∀ form∈scalarTail mode origin l t g node rule memory seed,StringReadWindows.Local mode form := by
  simp only [scalarTail,List.mem_append]
  intro form member
  rcases member with ((((input | direction) | head) | state) | failure) | jump
  · exact input_local mode l t _ form input
  · exact Listing8TailReadClasses.direction mode _ _ form direction
  · exact Listing8TailReadClasses.head mode _ _ form head
  · exact Listing8TailReadClasses.state mode _ _ form state
  · exact Listing8TailReadClasses.failure mode _ _ form failure
  · have whole:=Listing8TailReadClasses.jump_return mode origin
      (Listing8GraphBackedge.failed mode origin l t g node rule memory seed)
    exact whole form (List.mem_append_left _ jump)

/-- Both original copy source reads follow the actually executed bootstrap,
with no reset of memory or represented registers between the stages. -/
theorem copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing4EntryLayout.forms mode origin++Listing8GraphCopyWrites.copyForms mode l)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  rw [StringReadRuns.append,Listing8GraphEntryWrites.boot_run mode origin l t g node rule ctx memory seed]
  refine ⟨StringReadRuns.local_of_owned mode origin _ _ _ (Listing8TerminalReadClasses.entry mode origin)
    (Listing8GraphEntryWrites.boot_owned mode origin l t g node rule ctx memory seed),?_⟩
  rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed]
  exact Listing8CopyReads.original mode origin _ l _ ctx.resources
    (Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx) _ _

theorem contained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      (Listing8GraphJumpWrites.program mode origin l t g node rule memory seed)
      (Listing8GraphBackedge.initial mode origin l t g node rule memory seed) := by
  have owned:=Listing8GraphEntryWrites.owned mode origin l t g node rule ctx memory seed
  rw [program_split] at owned ⊢
  exact StringReadSuffix.contained mode origin _ _ _ _
    (copies mode origin l t g node rule ctx memory seed) (tail_local mode origin l t g node rule memory seed) owned

end SmcTuring.Appendix.Listing8GraphEntryReads

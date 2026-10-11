module
public import SmcTuring.Appendix.Listing8GlobalCopiedOwnerRegions
public import SmcTuring.Appendix.Listing8GlobalRetargetRegions

public section
namespace SmcTuring.Appendix.Listing8GlobalMainOwnerRegions
open Native Listing8CopyImage Listing8SourceGraph Listing8OwnerSequence
abbrev Targets:=Listing8PointerCopies.Targets

theorem pointer (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (source pc : Nat) (value : Word mode)
    (member : (.pointer source pc value : Owner mode)∈Listing8OwnerImage.owners mode l (values mode origin g node rule))
    (valueMember : value∈[(values mode origin g node rule).back,(values mode origin g node rule).forward,
      (values mode origin g node rule).next,(values mode origin g node rule).newState]) :
    Listing8GlobalCopiedOwnerRegions.Placement mode origin (.pointer source pc value) := by
  have original:=Listing8GlobalCopiedOwnerRegions.window mode origin l t g node rule ctx _ member
    (source,(Listing8Prototypes.pointerBytes mode source value).length) (by simp [Listing8OwnerSequence.windows])
  have copied:=Listing8GlobalCopiedOwnerRegions.window mode origin l t g node rule ctx _ member
    (pc,(Listing8Prototypes.pointerBytes mode source value).length) (by simp [Listing8OwnerSequence.windows])
  rw [Listing8Prototypes.pointer_length] at original copied
  exact ⟨original,copied,Listing8GlobalCopiedOwnerRegions.graph_word mode origin g node rule ctx.native value valueMember⟩

theorem placements (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ owner∈Listing8OwnerImage.owners mode l (values mode origin g node rule),Listing8GlobalCopiedOwnerRegions.Placement mode origin owner := by
  have input:=Listing8GlobalMainBounds.input mode origin l t g node rule ctx
  have direction:=Listing8GlobalMainBounds.direction mode origin l t g node rule ctx
  have scalar:=Listing8CopiedOwners.scalar_bounds mode l
  intro owner member
  simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointer mode origin l t g node rule ctx _ _ _ (by simp [Listing8OwnerImage.owners]) (by simp)
  · exact pointer mode origin l t g node rule ctx _ _ _ (by simp [Listing8OwnerImage.owners]) (by simp)
  · exact pointer mode origin l t g node rule ctx _ _ _ (by simp [Listing8OwnerImage.owners]) (by simp)
  · right;left;constructor <;> omega
  · right;left;constructor <;> omega
  · have inside : (Listing8DirectionGeometry.region mode l).start≤l.direction+6 ∧
        l.direction+10≤Listing8DirectionLayout.endPC mode (Listing8DirectionGeometry.region mode l) := by
      rw [ctx.body.state.head.direction]
      cases mode <;> simp [Listing8DirectionLayout.directionPC,Listing8DirectionLayout.maskPC,Listing8DirectionLayout.selectionEnd,
        Listing8DirectionLayout.combinedPC,Listing8DirectionLayout.forwardPC,Listing8DirectionLayout.notPC,
        Listing8DirectionLayout.backPC,Listing8DirectionLayout.copyStart,Listing8DirectionLayout.duplicateSpan,
        Listing8DirectionLayout.halves,Listing8PointerCopies.halfCount,DwordLayout.span,DwordLayout.storeSize,Listing8DirectionLayout.endPC] <;> omega
    right;left;constructor <;> omega
  · exact pointer mode origin l t g node rule ctx _ _ _ (by simp [Listing8OwnerImage.owners]) (by simp)

theorem owner_regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map (StringStoreWrites.liftDword mode))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) :=
  Listing8GlobalCopiedOwnerRegions.regions mode origin _ _ (Listing8CopiedOwners.chain mode l _)
    (Listing8CopiedOwners.valid mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx))
    (Listing8CopiedOwners.outside mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx))
    (placements mode origin l t g node rule ctx) _
    (Listing8MainRetarget.registers mode l _ ctx.resources ctx.fields.tapeReach state entry forward current).1
    (Listing8MainRetarget.owner_current mode l _ ctx.resources ctx.fields.tapeReach state entry forward current)

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((Listing8MainLiveOwners.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have trace:=StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources state entry forward current)
  rw [Listing8MainLiveOwners.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  exact ⟨Listing8GlobalRetargetRegions.regions mode origin l t g node rule ctx state entry forward current,
    owner_regions mode origin l t g node rule ctx state entry forward current⟩

end SmcTuring.Appendix.Listing8GlobalMainOwnerRegions

module
public import SmcTuring.Appendix.Listing8MainLiveOwners
public import SmcTuring.Appendix.Listing8MainRetargetWrites
public import SmcTuring.Appendix.Listing8GraphCopiedWriteBounds

public section
namespace SmcTuring.Appendix.Listing8MainOwnerWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets := Listing8PointerCopies.Targets

theorem owner_owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map
        (StringStoreWrites.liftDword mode))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) :=
  Listing8OwnerSequenceWrites.owned mode origin _ _ _ (Listing8CopiedOwners.chain mode l _)
    (Listing8CopiedOwners.valid mode l _ ctx.resources (owners mode origin l t g node rule ctx))
    (Listing8CopiedOwners.outside mode l _ ctx.resources (owners mode origin l t g node rule ctx))
    (Listing8GraphCopiedWriteBounds.placement mode origin l t g node rule ctx) _
    (Listing8MainRetarget.registers mode l _ ctx.resources ctx.fields.tapeReach state entry forward current).1
    (Listing8MainRetarget.owner_current mode l _ ctx.resources ctx.fields.tapeReach state entry forward current)

/-- All copied indirect targets and later owner packets follow from the
present main image and actual copy/retarget effects. -/
theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8MainLiveOwners.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  rw [Listing8MainLiveOwners.program,List.map_append]
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ state (Listing8MainRetarget.finish mode l (values mode origin g node rule) state)
  · exact StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources state entry forward current)
  · exact Listing8MainRetargetWrites.owned mode origin _ l _ ctx.resources
      (Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx)
      (Listing8GraphFieldWriteBounds.input mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward current
  · exact owner_owned mode origin l t g node rule ctx state entry forward current

theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStack.Trace mode state
      ((Listing8MainLiveOwners.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8MainLiveOwners.finish mode l (values mode origin g node rule) state) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8MainLiveOwners.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state :=
  ⟨StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.trace mode l _ ctx.resources
      (owners mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward current),
    owned mode origin l t g node rule ctx state entry forward current⟩

end SmcTuring.Appendix.Listing8MainOwnerWrites

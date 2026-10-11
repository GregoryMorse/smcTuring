module
public import SmcTuring.Appendix.Listing8MainOwnerWrites
public import SmcTuring.Appendix.Listing8MainGraphPrefix
public import SmcTuring.Appendix.Listing8GraphPointerWrites

public section
namespace SmcTuring.Appendix.Listing8MainPrefixWrites
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets := Listing8PointerCopies.Targets

/-- Complete repeated copy/retarget/owner/pointer prefix, with current
helper bytes and every indirect target derived across preceding execution. -/
theorem owned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainPrefix.Current mode l t (values mode origin g node rule) state.principal.memory) :
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  rw [Listing8MainPrefix.program,List.map_append]
  apply StackFieldWrites.owned_append mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
    _ _ state (Listing8MainLiveOwners.finish mode l (values mode origin g node rule) state)
  · exact StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.trace mode l _ ctx.resources
      (owners mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward current.copying)
  · exact Listing8MainOwnerWrites.owned mode origin l t g node rule ctx state entry forward current.copying
  · exact Listing8GraphPointerWrites.pointer_owned mode origin l t g node rule ctx _
      (Listing8MainLiveOwners.registers mode l _ ctx.resources (owners mode origin l t g node rule ctx)
        ctx.fields.tapeReach state entry forward current.copying).1

theorem execute (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainPrefix.Current mode l t (values mode origin g node rule) state.principal.memory) :
    StringStack.Trace mode state
      ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state) ∧
    StringWrites.OwnedRun mode origin (Listing8GraphLayout.endPC mode origin g.transitions g.nodes)
      ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state :=
  ⟨StringDwordWritesBridge.trace mode (Listing8MainPrefix.trace mode l t _
      (Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds state entry forward current),
    owned mode origin l t g node rule ctx state entry forward current⟩

end SmcTuring.Appendix.Listing8MainPrefixWrites

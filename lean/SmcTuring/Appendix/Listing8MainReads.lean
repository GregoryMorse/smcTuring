module
public import SmcTuring.Appendix.Listing8CopyReads
public import SmcTuring.Appendix.Listing8ScalarReadClasses
public import SmcTuring.Appendix.Listing8MainInputWrites

public section
namespace SmcTuring.Appendix.Listing8MainReads
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
attribute [local irreducible] StringWrites.OwnedRun StringReadRuns.Run

theorem retarget (mode : Mode) (start stop : Nat) (l : Layout) (v : Values mode)
    (resources : Resources mode l) (placed : Listing8CopyWriteBounds.Placement mode start stop l)
    (inputInside : start≤l.input.start ∧ Listing8LiteralInput.endPC mode l.input≤stop)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringReadRuns.Run mode ⟨start,stop⟩ ((Listing8MainRetarget.program mode l v).map (StringStoreWrites.liftDword mode)) state := by
  have copied:=Listing8CopyReads.live mode start stop l v resources placed state entry forward current
  have mapped : (((Listing8MainCopies.program mode l).map StringDword.Form.string).map (StringStoreWrites.liftDword mode))=
      (Listing8MainCopies.program mode l).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
  have localTail:=StringReadRuns.local_of_owned mode start stop _ _ (Listing8ScalarReadClasses.retarget mode l v)
    (Listing8MainRetargetWrites.retarget_owned mode start stop l v resources placed inputInside reach _
      (Listing8MainCopies.registers mode l v resources state entry forward current).1
      (Listing8MainCopies.retarget_current mode l v resources state entry forward current))
  rw [Listing8MainRetarget.program,List.map_append]
  apply StringReadRuns.append_trace mode ⟨start,stop⟩ _ _ state (Listing8MainCopies.finish mode l state)
  · exact StringDwordWritesBridge.trace mode (StringDword.string_trace mode (Listing8MainCopies.trace mode l v resources state entry forward current))
  · rw [mapped];exact copied
  · exact localTail

theorem owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      ((Listing8MainLiveOwners.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  rw [Listing8MainLiveOwners.program,List.map_append]
  apply StringReadRuns.append_trace mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
    _ _ state (Listing8MainRetarget.finish mode l (values mode origin g node rule) state)
  · exact StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources state entry forward current)
  · exact retarget mode origin _ l _ ctx.resources (Listing8GraphCopyWriteBounds.placement mode origin l t g node rule ctx)
      (Listing8GraphFieldWriteBounds.input mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward current
  · exact StringReadRuns.local_of_owned mode origin _ _ _ (Listing8ScalarReadClasses.owners mode _)
      (Listing8MainOwnerWrites.owner_owned mode origin l t g node rule ctx state entry forward current)

theorem main_prefix (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainPrefix.Current mode l t (values mode origin g node rule) state.principal.memory) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  rw [Listing8MainPrefix.program,List.map_append]
  apply StringReadRuns.append_trace mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
    _ _ state (Listing8MainLiveOwners.finish mode l (values mode origin g node rule) state)
  · exact StringDwordWritesBridge.trace mode (Listing8MainLiveOwners.trace mode l _ ctx.resources
      (Listing8GraphInputContext.owners mode origin l t g node rule ctx) ctx.fields.tapeReach state entry forward current.copying)
  · exact owners mode origin l t g node rule ctx state entry forward current.copying
  · exact StringReadRuns.local_of_owned mode origin _ _ _ (Listing8ScalarReadClasses.pointers mode l t)
      (Listing8GraphPointerWrites.pointer_owned mode origin l t g node rule ctx _
        (Listing8MainLiveOwners.registers mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx)
          ctx.fields.tapeReach state entry forward current.copying).1)

/-- The complete actual repeated main input prefix includes copy SI reads,
all pointer/owner reads and every comparison/mask/update read. Only present
maintained entry and original static Context are supplied. -/
theorem input (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode)
    (entry : Listing8MainGraphImage.Current mode origin l t g node rule old state) :
    StringReadRuns.Run mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
      ((Listing8MainInput.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)) state := by
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated entry
  rw [Listing8MainInput.program,List.map_append]
  apply StringReadRuns.append_trace mode ⟨origin,Listing8GraphLayout.endPC mode origin g.transitions g.nodes⟩
    _ _ state (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state)
  · exact (Listing8MainPrefixWrites.execute mode origin l t g node rule ctx state entry.entry entry.forward image.prefixCurrent).1
  · exact main_prefix mode origin l t g node rule ctx state entry.entry entry.forward image.prefixCurrent
  · exact StringReadRuns.local_of_owned mode origin _ _ _ (StringScalarLists.mixed mode _)
      (Listing8MainInputWrites.input_owned mode origin l t g node rule ctx old state entry)

end SmcTuring.Appendix.Listing8MainReads

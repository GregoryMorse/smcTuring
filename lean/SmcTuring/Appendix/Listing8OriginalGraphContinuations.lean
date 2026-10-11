module
public import SmcTuring.Appendix.Listing8OriginalGraphMainEntry

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphContinuations
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run

theorem global_after_boot (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GlobalControlTemplates.Property mode origin
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.memory := by
  have initial:=Listing8GlobalControlTemplates.initial mode origin _ (Listing8GlobalInitialControl.current mode origin l t g node rule ctx memory seed)
  have actual:=Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  change StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
    (Listing4EntryLayout.forms mode origin) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) at actual
  have regions:=BoundedStoreRegions.monotone mode (Listing4StackTemplates.Slots mode origin) (Listing8GlobalControlLayout.Allowed mode origin)
    _ _ (fun _ _ slots => Or.inl slots)
    (Listing4EntrySlotRegions.entry mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body))
  exact Listing8GlobalControlProperties.after_trace mode origin _ _ _ initial regions actual

theorem copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (Listing8JointOriginalGraphCopies.Property mode origin l g)
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) :=
  Listing8JointOriginalGraphCopies.pair mode origin l t g node rule ctx Listing8OriginalGraphMainEntry.old _
    (Listing8OriginalGraphMainEntry.current mode origin l t g node rule ctx memory seed)
    (global_after_boot mode origin l t g node rule ctx memory seed)

theorem retarget (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOriginalGraphRetarget.Property mode origin l
      (values mode origin g node rule) g reached.principal.memory)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8MainCopies.finish mode l (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)) :=
  Listing8JointOriginalGraphRetarget.retarget mode origin l t g node rule ctx Listing8OriginalGraphMainEntry.old _
    (Listing8OriginalGraphMainEntry.current mode origin l t g node rule ctx memory seed)
    (global_after_boot mode origin l t g node rule ctx memory seed)

theorem owner_pointer (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached => Listing8JointOriginalGraphFailure.Property mode origin l
      (values mode origin g node rule) g reached.principal.memory)
      (Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)) :=
  Listing8JointOriginalGraphOwner.owner_pointer mode origin l t g node rule ctx Listing8OriginalGraphMainEntry.old _
    (Listing8OriginalGraphMainEntry.current mode origin l t g node rule ctx memory seed)
    (global_after_boot mode origin l t g node rule ctx memory seed)

/-- One original image and actual bootstrap supply an appended full
copy/retarget/owner/pointer continuation with the SAME graph/global/macro
invariant; actual endpoint traces determine every continuation state. -/
theorem through_pointer (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (Listing8JointOriginalGraphMain.Property mode origin l (values mode origin g node rule) g)
      ((Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
  have graph:=Listing8OriginalGraphMainEntry.current mode origin l t g node rule ctx memory seed
  have image:=Listing8MainGraphImage.input_current mode origin l t g node rule Listing8OriginalGraphMainEntry.old _ ctx.nodeLocated ctx.ruleLocated graph
  have copyTrace:=(Listing8GraphCopyOwnerPrefixes.live mode origin l t g node rule ctx _ graph.entry graph.forward image.prefixCurrent.copying).1
  have first : StringTemplateStates.Run mode (Listing8JointOriginalGraphMain.Property mode origin l (values mode origin g node rule) g)
      ((Listing8MainRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) := by
    rw [Listing8JointRetargetControl.shape,StringTemplateStates.append,StringWrites.trace_run_eq mode copyTrace]
    exact ⟨StringTemplateStates.monotone mode _ _ _ _ (fun reached all =>
        show Listing8JointOriginalGraphMain.Property mode origin l (values mode origin g node rule) g reached from
        ⟨all.1,Listing8JointOriginalGraphMain.from_copy mode origin l _ g reached.principal.memory all.2⟩)
        (copies mode origin l t g node rule ctx memory seed),
      StringTemplateStates.monotone mode _ _ _ _ (fun reached all =>
        show Listing8JointOriginalGraphMain.Property mode origin l (values mode origin g node rule) g reached from
        ⟨⟨all.1.1,all.1.2.2.1,all.1.2.2.2⟩,Listing8JointOriginalGraphMain.from_phase mode origin l _ g reached.principal.memory all.2⟩)
        (retarget mode origin l t g node rule ctx memory seed)⟩
  have actual:=StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources _ graph.entry graph.forward image.prefixCurrent.copying)
  have shape : (Listing8MainPrefix.program mode l t (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)=
      (Listing8MainRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)++
        Listing8JointOwnerPointerCatalog.forms mode l t (values mode origin g node rule) := by
    simp only [Listing8MainPrefix.program,Listing8MainLiveOwners.program,Listing8JointOwnerPointerCatalog.forms,List.map_append,List.append_assoc]
  rw [shape,StringTemplateStates.append,StringWrites.trace_run_eq mode actual]
  exact ⟨first,StringTemplateStates.monotone mode _ _ _ _ (fun reached all =>
    show Listing8JointOriginalGraphMain.Property mode origin l (values mode origin g node rule) g reached from
    ⟨⟨all.1.1,all.1.2.2.1,all.1.2.2.2⟩,Listing8JointOriginalGraphMain.from_phase mode origin l _ g reached.principal.memory
      (Listing8JointOriginalGraphRetarget.from_fixed mode origin l _ g reached.principal.memory all.2)⟩)
    (owner_pointer mode origin l t g node rule ctx memory seed)⟩

end SmcTuring.Appendix.Listing8OriginalGraphContinuations

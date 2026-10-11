module
public import SmcTuring.Appendix.Listing8RetargetTapeTemplates
public import SmcTuring.Appendix.Listing8GlobalOriginalControlTemplates
public import SmcTuring.Appendix.Listing8GlobalMainControlTemplates
public import SmcTuring.Appendix.Listing8GraphCopyOwnerPrefixes
public import SmcTuring.Native.StringTemplateTraceSegments

public section
namespace SmcTuring.Appendix.Listing8JointRetargetControl
open Native Listing8CopyImage Listing8SourceGraph
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

theorem shape (mode : Mode) (l : Layout) (v : Values mode) :
    ((Listing8MainRetarget.program mode l v).map (StringStoreWrites.liftDword mode))=
      ((Listing8MainCopies.program mode l).map (StringWrites.liftString mode))++
      ((Listing8LiveRetarget.program mode l v).map (StringStoreWrites.liftDword mode)) := by
  rw [Listing8MainRetarget.program,List.map_append,List.map_map];rfl

/-- All eight actual retarget descriptors and global control decode together
at the identical actual main-trace retarget/tape-owner prefixes. -/
theorem maintained (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (old : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule old state) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      ∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),
        DwordTemplateCollection.Decodes mode template reached.principal.memory)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8MainCopies.finish mode l state) := by
  have current:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated image.body
  have copying:=current.state.head.input.prefixCurrent.copying
  have entry:=image.body.state.head.graph.entry
  have forward:=image.body.state.head.graph.forward
  have whole:=Listing8GlobalMainControlTemplates.execute mode origin l t g node rule ctx old state image
  have leading:=(Listing8GraphCopyOwnerPrefixes.live mode origin l t g node rule ctx state entry forward copying).1
  have short:=StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources state entry forward copying)
  rw [shape] at short
  have localKept:=Listing8RetargetTapeTemplates.actual_copies mode l _ ctx.resources ctx.fields.tapeReach state entry forward copying
  have size : (((Listing8MainCopies.program mode l).map (StringWrites.liftString mode))++
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))).length≤
      (Listing8LoopControl.program mode origin l t g node rule state).length := by
    rw [←shape,List.length_map,Listing8MainRetarget.instruction_count,Listing8LoopControl.instruction_count]
    cases mode <;> decide
  exact StringTemplateTraceSegments.join_segment mode _ _ _ _ _ state _ _ _ size leading short whole.1 whole.2 localKept

/-- The original bootstrap and both copies are actual prefixes of the same
147/195-instruction initial main/control execution. Future images are derived. -/
theorem original (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions)
    (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      ∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),
        DwordTemplateCollection.Decodes mode template reached.principal.memory)
      ((Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode))
      (Listing8MainCopies.finish mode l (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed)) := by
  have copying:=Listing8GlobalOriginalPrefix.copying mode origin l t g node rule ctx memory seed
  have entry : (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).principal.pc=Arithmetic.encodeNat mode l.start := by
    rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  have forward : (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed).backwards=false := by
    rw [Listing8GraphCopyWrites.body_entry mode origin l t g node rule ctx memory seed];rfl
  have boot:=Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule memory seed)
    (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  change StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed)
    (Listing4EntryLayout.forms mode origin) (Listing8GraphCopyWrites.afterBoot mode origin l t g node rule memory seed) at boot
  have copies:=(Listing8GraphCopyOwnerPrefixes.live mode origin l t g node rule ctx _ entry forward copying).1
  have retarget:=StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l _ ctx.resources _ entry forward copying)
  rw [shape] at retarget
  have short:=StringStack.trace_append mode boot retarget
  rw [←List.append_assoc] at short
  have leading:=StringStack.trace_append mode boot copies
  have whole:=Listing8GlobalOriginalControlTemplates.execute mode origin l t g node rule ctx memory seed
  have localKept:=Listing8RetargetTapeTemplates.actual_copies mode l _ ctx.resources ctx.fields.tapeReach _ entry forward copying
  have size : ((Listing4EntryLayout.forms mode origin++(Listing8MainCopies.program mode l).map (StringWrites.liftString mode))++
      (Listing8LiveRetarget.program mode l (values mode origin g node rule)).map (StringStoreWrites.liftDword mode)).length≤
      (Listing8GlobalOriginalControlTemplates.program mode origin l t g node rule memory seed).length := by
    rw [List.append_assoc,←shape,List.length_append,List.length_map,Listing4EntryLayout.instruction_count,
      Listing8MainRetarget.instruction_count,Listing8GlobalOriginalControlTemplates.instruction_count]
    cases mode <;> decide
  exact StringTemplateTraceSegments.join_segment mode _ _ _ _ _ _ _ _ _ size leading short whole.1 whole.2 localKept

end SmcTuring.Appendix.Listing8JointRetargetControl

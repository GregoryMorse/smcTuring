module
public import SmcTuring.Appendix.Listing8RetargetOwnerFields
public import SmcTuring.Appendix.Listing8JointCopiedOwnerTemplates

public section
namespace SmcTuring.Appendix.Listing8RetargetOwnerCatalog
open Native Listing8CopyImage Listing8SourceGraph Listing8OwnerSequence
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

theorem initial (mode : Mode) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    DwordTemplateCollection.All (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l))
      (Listing8MainRetarget.finish mode l v state).principal.memory := by
  have kept:=Listing8RetargetTapeTemplates.all_states mode l v resources reach _
    (Listing8MainCopies.registers mode l v resources state entry forward current).1
    (Listing8MainCopies.retarget_current mode l v resources state entry forward current)
  have ending:=StringTemplateStates.at_prefix mode _ _ [] (Listing8MainCopies.finish mode l state)
    (by simpa only [List.append_nil] using kept)
  rw [StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode
    (Listing8MainRetarget.retarget_trace mode l v resources state entry forward current))] at ending
  exact ending

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode
      (DwordTemplateCollection.CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)))
      ((program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map (StringStoreWrites.liftDword mode))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) :=
  Listing8OwnerStoreRegions.regions mode _ _ _ (Listing8CopiedOwners.chain mode l _)
    (Listing8CopiedOwners.valid mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx))
    (Listing8CopiedOwners.outside mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx))
    (Listing8RetargetOwnerFields.placements mode origin l t g node rule ctx) _
    (Listing8MainRetarget.registers mode l _ ctx.resources ctx.fields.tapeReach state entry forward current).1
    (Listing8MainRetarget.owner_current mode l _ ctx.resources ctx.fields.tapeReach state entry forward current)

/-- The retarget catalog survives ALL later copied-owner instructions, at
the same native prefixes as global control and exact active-word ownership. -/
theorem main (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory)
    (global : Listing8GlobalControlTemplates.Property mode origin state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      Listing8GlobalControlTemplates.Decodes mode origin reached.principal.memory ∧
      Listing8CopiedOwnerActiveRun.Certificate mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)) reached.principal.memory ∧
      ∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),
        DwordTemplateCollection.Decodes mode template reached.principal.memory)
      ((program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map (StringStoreWrites.liftDword mode))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have owned:=Listing8JointCopiedOwnerTemplates.main mode origin l t g node rule ctx state entry forward current global
  have kept:=StringStoreRegions.arithmetic_states mode _ _ _
    (initial mode l _ ctx.resources ctx.fields.tapeReach state entry forward current)
    (regions mode origin l t g node rule ctx state entry forward current)
  have decoded:=StringTemplateStates.monotone mode _ _ _ _
    (fun reached all template member => DwordTemplateCollection.decodes mode template reached.principal.memory (all template member)) kept
  exact StringTemplateStates.monotone mode _ _ _ _ (fun _ both => ⟨both.1.1,both.1.2,both.2⟩)
    (JointTemplateStates.join mode _ _ _ _ owned decoded)

end SmcTuring.Appendix.Listing8RetargetOwnerCatalog

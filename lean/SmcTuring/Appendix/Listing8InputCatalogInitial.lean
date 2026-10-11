module
public import SmcTuring.Appendix.Listing8InputCrossCatalogFields
public import SmcTuring.Appendix.Listing8RetargetOwnerCatalog

public section
namespace SmcTuring.Appendix.Listing8InputCatalogInitial
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def Property (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory) : Prop :=
  DwordTemplateCollection.All (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) memory ∧
    Listing8MacroPointerFrames.Property mode l memory ∧
    Listing8OwnerTemplateCollection.All mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l v)) memory

theorem endpoint (mode : Mode) (property : ByteMemory.Memory → Prop) (forms : List (StringStack.Form mode))
    (state finish : StringExecution.State mode) (run : StringTemplateStates.Run mode (fun reached => property reached.principal.memory) forms state)
    (trace : StringStack.Trace mode state forms finish) : property finish.principal.memory := by
  have last:=StringTemplateStates.at_prefix mode _ forms [] state (by simpa only [List.append_nil] using run)
  rw [StringWrites.trace_run_eq mode trace] at last
  exact last

theorem retarget (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainPrefix.Current mode l t (values mode origin g node rule) state.principal.memory) :
    DwordTemplateCollection.All (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have bounds:=(Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds
  have ownBounds:=Listing8GraphInputContext.owners mode origin l t g node rule ctx
  have first:=StringStoreRegions.arithmetic_states mode _ _ _
    (Listing8RetargetOwnerCatalog.initial mode l _ ctx.resources ctx.fields.tapeReach state entry forward current.copying)
    (Listing8RetargetOwnerCatalog.regions mode origin l t g node rule ctx state entry forward current.copying)
  have ownerAt:=endpoint mode _ _ _ _ first (StringDwordWritesBridge.trace mode
    (Listing8MainLiveOwners.owner_trace mode l _ ctx.resources ownBounds ctx.fields.tapeReach state entry forward current.copying))
  have location:=(Listing8MainLiveOwners.registers mode l _ ctx.resources ownBounds ctx.fields.tapeReach state entry forward current.copying).1
  exact endpoint mode _ _ _ _ (StringStoreRegions.arithmetic_states mode _ _ _ ownerAt
    (Listing8RetargetPointerFields.regions mode l t ctx.copies _ location))
    (StringDwordWritesBridge.trace mode (Listing8MainPrefix.pointer_trace mode l t _ bounds state entry forward current))

theorem macros (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainPrefix.Current mode l t (values mode origin g node rule) state.principal.memory) :
    Listing8MacroPointerFrames.Property mode l (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have bounds:=(Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds
  have ownBounds:=Listing8GraphInputContext.owners mode origin l t g node rule ctx
  have first:=StringStoreTemplateRuns.preserve mode (fun address _ => patchStart mode l≤address)
    (Listing8MacroPointerFrames.Property mode l) _ _
    (Listing8MacroOwnerFrames.initial mode l _ ctx.resources ctx.fields.tapeReach state entry forward current.copying)
    (fun memory address packet both after => Listing8MacroPointerFrames.store mode l memory address packet both (Or.inl after))
    (Listing8MacroOwnerFrames.regions mode origin l t g node rule ctx state entry forward current.copying)
  have ownerAt:=endpoint mode _ _ _ _ first (StringDwordWritesBridge.trace mode
    (Listing8MainLiveOwners.owner_trace mode l _ ctx.resources ownBounds ctx.fields.tapeReach state entry forward current.copying))
  have location:=(Listing8MainLiveOwners.registers mode l _ ctx.resources ownBounds ctx.fields.tapeReach state entry forward current.copying).1
  exact endpoint mode _ _ _ _ (Listing8MacroPointerFrames.all_states mode l t ctx.copies _ location ownerAt)
    (StringDwordWritesBridge.trace mode (Listing8MainPrefix.pointer_trace mode l t _ bounds state entry forward current))

theorem owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainPrefix.Current mode l t (values mode origin g node rule) state.principal.memory) :
    Listing8OwnerTemplateCollection.All mode (Listing8CopiedOwnerCatalog.catalog mode (Listing8OwnerImage.owners mode l (values mode origin g node rule)))
      (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory := by
  have bounds:=(Listing8MainGraphPrefix.bounds mode origin l t g node rule ctx).input.prefixBounds
  have ownBounds:=Listing8GraphInputContext.owners mode origin l t g node rule ctx
  have present:=Listing8CopiedOwnerCatalog.all_current mode _ _
    (Listing8MainLiveOwners.retained_image mode l _ ctx.resources ownBounds ctx.fields.tapeReach state entry forward current.copying)
  have location:=(Listing8MainLiveOwners.registers mode l _ ctx.resources ownBounds ctx.fields.tapeReach state entry forward current.copying).1
  exact endpoint mode _ _ _ _ (Listing8OwnerPointerFrames.all_states mode origin l t g node rule ctx _ location present)
    (StringDwordWritesBridge.trace mode (Listing8MainPrefix.pointer_trace mode l t _ bounds state entry forward current))

theorem initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainPrefix.Current mode l t (values mode origin g node rule) state.principal.memory) :
    Property mode l (values mode origin g node rule) (Listing8MainPrefix.finish mode l t (values mode origin g node rule) state).principal.memory :=
  ⟨retarget mode origin l t g node rule ctx state entry forward current,
    macros mode origin l t g node rule ctx state entry forward current,
    owners mode origin l t g node rule ctx state entry forward current⟩

end SmcTuring.Appendix.Listing8InputCatalogInitial

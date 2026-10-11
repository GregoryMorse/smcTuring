module
public import SmcTuring.Appendix.Listing8InputRetargetTemplateBindings
public import SmcTuring.Native.StringDwordWritesBridge

public section
namespace SmcTuring.Appendix.Listing8RetargetTapeTemplates
open Native Listing8CopyImage Listing8Prototypes DwordTemplateCollection

theorem tape_field (mode : Mode) (l : Layout) (r : Resources mode l) :
    CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l))
      (Listing8LiteralInput.sourceField mode l.input) 4 := by
  intro template member
  have range := Listing8RetargetExecutableTemplates.bounds mode (patchLayout mode l) template member
  have after := r.inputAfter
  have field := (Listing8OwnerImage.source_field_bounds mode l).1
  change Listing8ModeOffsets.endPC mode (patchLayout mode l)≤l.input.start at after
  exact Or.inr (Or.inr (by omega))

/-- The fifth actual instruction is the copied tape owner. Its full target
window is derived at the post-patch PC; it preserves all eight descriptors. -/
theorem all_states (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Listing8LiveRetarget.Current mode l v state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      All (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l)) reached.principal.memory)
      ((Listing8LiveRetarget.program mode l v).map (StringStoreWrites.liftDword mode)) state := by
  have first := Listing8RetargetExecutableTemplates.all_states mode (patchLayout mode l) l.sourceNode l.sourceTransition
    v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState (block_capacity mode l r) state entry current
  rw [Listing8InputRetargetTemplateBindings.retarget_forms] at first
  have run := StringWrites.trace_run_eq mode
    (StringDwordWritesBridge.trace mode (Listing8LiveRetarget.patch_trace mode l v r state entry current))
  have atEnd := StringTemplateStates.at_prefix mode _ _ [] state (by simpa only [List.append_nil] using first)
  rw [run] at atEnd
  have fits := Listing8OwnerImage.source_field_fits mode l r
  have located := MixedFieldOwnership.located mode (nodeParams mode l).destination
    (Listing8LiteralInput.sourceField mode l.input) (.store 0 v.tape) (Listing8LiveRetarget.patched mode l state).principal
    rfl (Listing8LiveRetarget.patched_pc mode l r state entry) reach (by omega)
    (CompatibleAll (Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l))) (tape_field mode l r)
  have kept := DwordTemplateCollection.execute mode _
    (.arithmetic (DwordRetarget.ownerForm mode (nodeParams mode l).destination (Listing8LiteralInput.sourceField mode l.input) v.tape))
    (Listing8LiveRetarget.patched mode l state) atEnd located
  have canonical : StringMixed.canonical mode
      (.arithmetic (DwordRetarget.ownerForm mode (nodeParams mode l).destination (Listing8LiteralInput.sourceField mode l.input) v.tape))=
      Listing8Initializer.tapeForm mode l v := by cases mode <;> rfl
  rw [canonical] at kept
  rw [Listing8LiveRetarget.program,List.map_append,StringTemplateStates.append,run]
  exact ⟨first,⟨atEnd,kept⟩⟩

theorem all_decodes (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Listing8LiveRetarget.Current mode l v state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      ∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),Decodes mode template reached.principal.memory)
      ((Listing8LiveRetarget.program mode l v).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun reached all template member => decodes mode template reached.principal.memory (all template member))
    (all_states mode l v r reach state entry current)

theorem actual_copies (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      ∀ template∈Listing8RetargetExecutableTemplates.templates mode (patchLayout mode l),Decodes mode template reached.principal.memory)
      ((Listing8LiveRetarget.program mode l v).map (StringStoreWrites.liftDword mode))
      (Listing8MainCopies.finish mode l state) :=
  all_decodes mode l v r reach _ (Listing8MainCopies.registers mode l v r state entry forward current).1
    (Listing8MainCopies.retarget_current mode l v r state entry forward current)

end SmcTuring.Appendix.Listing8RetargetTapeTemplates

module
public import SmcTuring.Appendix.Listing8MacroPointerFrames

public section
namespace SmcTuring.Appendix.Listing8MacroRetargetFrames
open Native Listing8CopyImage Listing8Prototypes
attribute [local irreducible] StringTemplateStates.Run

theorem prefix_window (mode : Mode) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory)
    (observed count : Nat) (before : observed+count≤patchStart mode l) :
    ByteMemory.bytesAt (Listing8MainCopies.finish mode l state).principal.memory observed count=
      ByteMemory.bytesAt state.principal.memory observed count := by
  apply Listing8MainCopies.window mode l v resources state entry forward current
  · right;dsimp [nodeParams,Listing8ModeOffsets.nodeEntry,patchLayout];omega
  · right;dsimp [transitionParams,Listing8ModeOffsets.transitionEntry,Listing8ModeOffsets.nodeEntry,patchLayout];omega

theorem initial (mode : Mode) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    Listing8MacroPointerFrames.Property mode l (Listing8MainCopies.finish mode l state).principal.memory := by
  have coords:=coordinates mode l
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  constructor
  · apply StringMacroTemplates.initial
    exact (prefix_window mode l v resources state entry forward current _ _ (coords.1.le.trans second)).trans
      (Listing8MainCopyImage.node_current mode l v _ current)
  · apply StringMacroTemplates.initial
    exact (prefix_window mode l v resources state entry forward current _ _ coords.2.1.le).trans
      (Listing8MainCopyImage.rule_current mode l v _ current)

theorem regions (mode : Mode) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Listing8LiveRetarget.Current mode l v state.principal.memory) :
    StringStoreRegions.Run mode (fun address _ => patchStart mode l≤address)
      ((Listing8LiveRetarget.program mode l v).map (StringStoreWrites.liftDword mode)) state := by
  have patches:=StringRetargetWrites.owned mode (patchStart mode l) (codeEnd mode l)
    _ (patchStart mode l) (Listing8ModeOffsets.chain mode (patchLayout mode l))
    (Listing8ModeOffsets.valid mode _ (block_capacity mode l resources) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)))
    (fun site member => by
      have bound:=Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member
      change patchStart mode l+40≤site.owner ∧ site.owner+10≤codeEnd mode l ∧ _ at bound
      constructor <;> omega) state entry
  have trace:=StringDwordWritesBridge.trace mode (Listing8LiveRetarget.patch_trace mode l v resources state entry current)
  have fits:=Listing8OwnerImage.source_field_fits mode l resources
  have field:=(Listing8OwnerImage.source_field_bounds mode l).1
  have after:=resources.inputAfter
  have lower : patchStart mode l≤Listing8LiteralInput.sourceField mode l.input := by
    change Listing8ModeOffsets.endPC mode (patchLayout mode l)≤l.input.start at after
    have bound:=(coordinates mode l).2.2
    change codeEnd mode l≤l.input.start at after
    omega
  rw [Listing8LiveRetarget.program,List.map_append,StringStoreRegions.append,StringWrites.trace_run_eq mode trace]
  constructor
  · exact BoundedStoreRegions.interval mode _ _ _ _ state (fun _ _ lo _ => lo) patches
  · exact BoundedStoreRegions.interval mode _ _ _ _ _ (fun _ _ lo _ => lo)
      ⟨StringStoreWrites.located mode (patchStart mode l) (Listing8LiteralInput.sourceField mode l.input+4)
        (nodeParams mode l).destination (Listing8LiteralInput.sourceField mode l.input) v.tape _
        (Listing8LiveRetarget.patched_pc mode l resources state entry) reach fits ⟨lower,by omega⟩,trivial⟩

theorem all_states (mode : Mode) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8MacroPointerFrames.Property mode l reached.principal.memory)
      ((Listing8LiveRetarget.program mode l v).map (StringStoreWrites.liftDword mode)) (Listing8MainCopies.finish mode l state) :=
  StringStoreTemplateRuns.preserve mode (fun address _ => patchStart mode l≤address)
    (Listing8MacroPointerFrames.Property mode l) _ _ (initial mode l v resources state entry forward current)
    (fun memory address packet both after => Listing8MacroPointerFrames.store mode l memory address packet both (Or.inl after))
    (regions mode l v resources reach _ (Listing8MainCopies.registers mode l v resources state entry forward current).1
      (Listing8MainCopies.retarget_current mode l v resources state entry forward current))

end SmcTuring.Appendix.Listing8MacroRetargetFrames

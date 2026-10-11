module
public import SmcTuring.Appendix.Listing8CopyWrites
public import SmcTuring.Native.StringRetargetWrites
public import SmcTuring.Appendix.Listing8Initializer

public section
namespace SmcTuring.Appendix.Listing8InitializerWrites
open Native Listing8CopyImage
abbrev Placement:=Listing8CopyWriteBounds.Placement

theorem patch_fields (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (placed : Placement mode codeStart codeEnd l) :
    ∀ site∈Listing8ModeOffsets.sites mode (patchLayout mode l),codeStart≤site.owner+2 ∧ site.owner+6≤codeEnd := by
  have coords:=coordinates mode l
  have before:=endpoint_lower mode l.start (Listing8Prototypes.nodeSpan mode)
  change l.start≤secondStart mode l at before
  have next:=endpoint_lower mode (secondStart mode l) (Listing8Prototypes.transitionSpan mode)
  change secondStart mode l≤patchStart mode l at next
  have block:=placed.block
  intro site member
  have bounds:=Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member
  change patchStart mode l+40≤site.owner ∧ site.owner+10≤Listing8CopyImage.codeEnd mode l ∧ _ at bounds
  exact ⟨by omega,by omega⟩

theorem tape_bounds (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (r : Resources mode l)
    (inputInside : codeStart≤l.input.start ∧ Listing8LiteralInput.endPC mode l.input≤codeEnd) :
    Listing8LiteralInput.sourceField mode l.input<2^(8*mode.wordBytes) ∧
    codeStart≤Listing8LiteralInput.sourceField mode l.input ∧ Listing8LiteralInput.sourceField mode l.input+4≤codeEnd := by
  have source:=(Listing8LiteralInput.positions mode l.input).2.2.1
  have ending:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  have capacity:=r.inputFits
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at source ending <;> exact ⟨by omega,by omega,by omega⟩

/-- Both copies, the four retargets and the first copied tape store have
code-owned architectural writes in their actual order and current states. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (v : Values mode) (r : Resources mode l)
    (placed : Placement mode codeStart codeEnd l)
    (inputInside : codeStart≤l.input.start ∧ Listing8LiteralInput.endPC mode l.input≤codeEnd)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8Initializer.program mode l v).map (StringStoreWrites.liftDword mode))
      (initial mode l v backing seed) := by
  let start:=initial mode l v backing seed
  have cp:=Listing8CopyWrites.copies mode codeStart codeEnd l v r placed backing seed
  have copyMapped : (((Listing8CopyTrace.program mode l).map StringDword.Form.string).map (StringStoreWrites.liftDword mode))=
      (Listing8CopyTrace.program mode l).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
  have copyOwned : StringWrites.OwnedRun mode codeStart codeEnd
      (((Listing8CopyTrace.program mode l).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)) start := by
    rw [copyMapped];exact cp.2
  have copyRun : StringWrites.run mode (((Listing8CopyTrace.program mode l).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)) start=
      Listing8CopyTrace.both mode l start := by rw [copyMapped];exact StringWrites.trace_run_eq mode cp.1
  have patches:=StringRetargetWrites.owned mode codeStart codeEnd _ (patchStart mode l) (Listing8ModeOffsets.chain mode (patchLayout mode l))
    (Listing8ModeOffsets.valid mode _ (block_capacity mode l r) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)))
    (patch_fields mode codeStart codeEnd l placed) (Listing8CopyTrace.both mode l start) (Listing8CopyTrace.patch_entry mode l v r backing seed)
  have patchTrace:=StringStack.previous_trace mode (StringControl.previous_trace mode (Listing8Initializer.patch_trace mode l v r backing seed))
  have patchRun : StringWrites.run mode ((StringRetarget.program mode (Listing8ModeOffsets.sites mode (patchLayout mode l))).map (StringStoreWrites.liftDword mode))
      (Listing8CopyTrace.both mode l start)=Listing8Initializer.patched mode l start := by
    apply StringWrites.trace_run_eq mode
    change StringStack.Trace mode (Listing8CopyTrace.both mode l start)
      ((StringRetarget.program mode (Listing8ModeOffsets.sites mode (patchLayout mode l))).map
        (fun form => StringStack.Form.previous (StringControl.Form.previous form))) (Listing8Initializer.patched mode l start)
    simpa only [List.map_map,Function.comp_def] using patchTrace
  have bounds:=tape_bounds mode codeStart codeEnd l r inputInside
  have last:=StringStoreWrites.located mode codeStart codeEnd (nodeParams mode l).destination (Listing8LiteralInput.sourceField mode l.input)
    v.tape (Listing8Initializer.patched mode l start) (Listing8Initializer.patched_pc mode l v r backing seed) reach bounds.1 bounds.2
  rw [Listing8Initializer.program,List.map_append,List.map_append,StringWrites.owned_run_append,StringWrites.owned_run_append,StringWrites.run_append,
    copyRun,patchRun]
  exact ⟨⟨copyOwned,patches⟩,last,trivial⟩

end SmcTuring.Appendix.Listing8InitializerWrites

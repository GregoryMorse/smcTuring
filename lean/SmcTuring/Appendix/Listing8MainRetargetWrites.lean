module
public import SmcTuring.Appendix.Listing8MainRetarget
public import SmcTuring.Appendix.Listing8MainCopyWrites
public import SmcTuring.Appendix.Listing8InitializerWrites
public import SmcTuring.Native.StringDwordWritesBridge

public section
namespace SmcTuring.Appendix.Listing8MainRetargetWrites
open Native Listing8CopyImage
abbrev Placement := Listing8CopyWriteBounds.Placement

theorem retarget_owned (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (v : Values mode)
    (resources : Resources mode l) (placed : Placement mode codeStart codeEnd l)
    (inputInside : codeStart≤l.input.start ∧ Listing8LiteralInput.endPC mode l.input≤codeEnd)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Listing8LiveRetarget.Current mode l v state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd
      ((Listing8LiveRetarget.program mode l v).map (StringStoreWrites.liftDword mode)) state := by
  have bounds := Listing8InitializerWrites.tape_bounds mode codeStart codeEnd l resources inputInside
  rw [Listing8LiveRetarget.program,List.map_append]
  apply StackFieldWrites.owned_append mode codeStart codeEnd _ _ state (Listing8LiveRetarget.patched mode l state)
  · exact StringDwordWritesBridge.trace mode (Listing8LiveRetarget.patch_trace mode l v resources state entry current)
  · exact StringRetargetWrites.owned mode codeStart codeEnd _ (patchStart mode l)
      (Listing8ModeOffsets.chain mode (patchLayout mode l))
      (Listing8ModeOffsets.valid mode _ (block_capacity mode l resources) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)))
      (Listing8InitializerWrites.patch_fields mode codeStart codeEnd l placed) state entry
  · exact ⟨StringStoreWrites.located mode codeStart codeEnd (nodeParams mode l).destination
      (Listing8LiteralInput.sourceField mode l.input) v.tape _
      (Listing8LiveRetarget.patched_pc mode l resources state entry) reach bounds.1 bounds.2,trivial⟩

/-- Present copy/source bytes derive the reached retarget image; ownership
is concluded for the complete 50/52 instruction prefix without initialization. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (v : Values mode)
    (resources : Resources mode l) (placed : Placement mode codeStart codeEnd l)
    (inputInside : codeStart≤l.input.start ∧ Listing8LiteralInput.endPC mode l.input≤codeEnd)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd
      ((Listing8MainRetarget.program mode l v).map (StringStoreWrites.liftDword mode)) state := by
  rw [Listing8MainRetarget.program,List.map_append]
  apply StackFieldWrites.owned_append mode codeStart codeEnd _ _ state (Listing8MainCopies.finish mode l state)
  · exact StringDwordWritesBridge.trace mode (StringDword.string_trace mode
      (Listing8MainCopies.trace mode l v resources state entry forward current))
  · have mapped : (((Listing8MainCopies.program mode l).map StringDword.Form.string).map (StringStoreWrites.liftDword mode))=
        (Listing8MainCopies.program mode l).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
    rw [mapped]
    exact Listing8MainCopyWrites.owned mode codeStart codeEnd l v resources placed state entry forward current
  · exact retarget_owned mode codeStart codeEnd l v resources placed inputInside reach _
      (Listing8MainCopies.registers mode l v resources state entry forward current).1
      (Listing8MainCopies.retarget_current mode l v resources state entry forward current)

theorem execute (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (v : Values mode)
    (resources : Resources mode l) (placed : Placement mode codeStart codeEnd l)
    (inputInside : codeStart≤l.input.start ∧ Listing8LiteralInput.endPC mode l.input≤codeEnd)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringStack.Trace mode state ((Listing8MainRetarget.program mode l v).map (StringStoreWrites.liftDword mode))
      (Listing8MainRetarget.finish mode l v state) ∧
    StringWrites.OwnedRun mode codeStart codeEnd
      ((Listing8MainRetarget.program mode l v).map (StringStoreWrites.liftDword mode)) state :=
  ⟨StringDwordWritesBridge.trace mode (Listing8MainRetarget.trace mode l v resources state entry forward current),
    owned mode codeStart codeEnd l v resources placed inputInside reach state entry forward current⟩

end SmcTuring.Appendix.Listing8MainRetargetWrites

module
public import SmcTuring.Appendix.Listing8LiteralComposition
public import SmcTuring.Appendix.Listing8InputMask
public import SmcTuring.Appendix.DwordComparisonTailWrites
public import SmcTuring.Native.DwordMixedWrites

public section
namespace SmcTuring.Appendix.Listing8LiteralInputWrites
open Native Listing8LiteralInput

/-- Static complete code spans only; no current or future state is a field. -/
structure Placement (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) : Prop where
  input : codeStart≤layout.start ∧ endPC mode layout≤codeEnd
  cursor : codeStart≤layout.cursor ∧ layout.cursor+mode.wordBytes≤codeEnd
  tape : codeStart≤layout.head+6 ∧ layout.head+10≤codeEnd
  masks : ∀ helper∈distributionLayouts mode layout,
    codeStart≤helper.destination ∧ helper.destination+4≤codeEnd

theorem fields (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (placed : Placement mode codeStart codeEnd layout) :
    (codeStart≤scalarField mode layout ∧ scalarField mode layout+4≤codeEnd) ∧
    (codeStart≤sourceField mode layout ∧ sourceField mode layout+4≤codeEnd) ∧
    (codeStart≤maskField mode layout ∧ maskField mode layout+4≤codeEnd) ∧
    (codeStart≤pendingField mode layout ∧ pendingField mode layout+4≤codeEnd) := by
  have input:=placed.input
  have ⟨owner,scalar,source,dist,update,mask,pending,ending⟩:=positions mode layout
  rw [ending] at input
  rw [scalar,source,mask,pending]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at input ⊢ <;> omega

/-- Ownership of the literal nine-instruction equality prefix includes its
temporary exchange and unchanged scalar-owner store. -/
theorem prefix_owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (placed : Placement mode codeStart codeEnd layout)
    (candidate ruleOld targetOld fresh : Dword) (capacity : endPC mode layout<2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    MixedDword.OwnedRun mode (fun address width => codeStart≤address ∧ address+width≤codeEnd)
      (prefixProgram mode layout candidate ruleOld) state := by
  have ⟨scalar,source,mask,pending⟩:=fields mode codeStart codeEnd layout placed
  have v:=tail_valid mode layout capacity
  have scalarFits:=v.scalarFits;have maskFits:=v.maskFits
  simp only [tailLayout] at scalarFits maskFits
  have a:=MixedLocatedWrites.field mode codeStart codeEnd layout.start (maskField mode layout) (.store 0 0) state rfl entry
    (by intro long;subst mode;simp [maskField,updateStart,distributionStart,ownerPC,copyStart,gap,DwordLayout.span,
        DwordLayout.storeSize,DwordArithmetic.length,Relocation.SignedDelta,Relocation.delta];omega)
    (by omega) mask
  have resetPC : (resetState mode layout state).pc=Arithmetic.encodeNat mode (copyLayout mode layout).start := by
    rw [reset_effect mode layout capacity state entry];rfl
  have b:=DwordMixedWrites.copy_owned mode codeStart codeEnd (copyLayout mode layout) (copy_admissible mode layout capacity)
    (resetState mode layout state) resetPC source pending
  have copyPC : (copiedState mode layout state).pc=Arithmetic.encodeNat mode (ownerPC mode layout) := by
    rw [copied_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have c:=MixedLocatedWrites.field mode codeStart codeEnd (ownerPC mode layout) (scalarField mode layout) (.store 0 candidate)
    (copiedState mode layout state) rfl copyPC
    (by intro long;simpa only [scalarField,DwordArithmetic.length] using DwordOwner.reach (ownerPC mode layout))
    (by omega) scalar
  have ownerPC : (ownerState mode layout candidate state).pc=Arithmetic.encodeNat mode ((tailLayout mode layout).start+10) := by
    rw [owner_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact];rfl
  have d:=DwordComparisonTailWrites.owned mode codeStart codeEnd (tailLayout mode layout) v ruleOld
    (ownerState mode layout candidate state) ownerPC scalar mask
  exact ⟨a,b.1,b.2.1,b.2.2.1,c,d.1,d.2.1,d.2.2.1,d.2.2.2.1,trivial⟩

/-- Every literal input-phase instruction has an actual nonempty code store.
Future helper bytes, cursor and PCs follow from the initial current packet. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (placed : Placement mode codeStart codeEnd layout)
    (candidate ruleOld targetOld fresh : Dword) (capacity : endPC mode layout<2^(8*mode.wordBytes))
    (masks : Listing8LiteralMaskTrace.Valid mode layout) (update : InputUpdate.Valid mode (updateLayout mode layout))
    (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    MixedDword.OwnedRun mode (fun address width => codeStart≤address ∧ address+width≤codeEnd)
      (Listing8LiteralComposition.program mode layout candidate ruleOld fresh) state := by
  have first:=prefix_owned mode codeStart codeEnd layout placed candidate ruleOld targetOld fresh capacity state entry intact
  have ⟨scalar,source,mask,pending⟩:=fields mode codeStart codeEnd layout placed
  have prefixPC:=prefix_pc mode layout candidate ruleOld targetOld fresh capacity state entry intact
  have second:=DwordMixedWrites.sequence_owned mode codeStart codeEnd (distributionLayouts mode layout) _
    (Listing8LiteralMaskTrace.chain mode layout) (Listing8LiteralMaskTrace.copies_valid mode layout capacity masks)
    (by intro helper member;rw [(Listing8LiteralMaskTrace.helper_bounds mode layout helper member).2.2];exact ⟨mask,placed.masks helper member⟩)
    (prefixState mode layout candidate ruleOld state) prefixPC
  have third:=InputUpdateTrace.pure mode (updateLayout mode layout) update ruleOld fresh (chosen candidate ruleOld)
    (Listing8LiteralComposition.distributedState mode layout candidate ruleOld state)
    (Listing8LiteralComposition.distribution_pc mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
    (Listing8LiteralComposition.distribution_update_intact mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
    ((Listing8LiteralComposition.distribution_cursor mode layout candidate ruleOld targetOld fresh capacity masks outside state entry intact).trans cursor)
    (fun address width => codeStart≤address ∧ address+width≤codeEnd) pending placed.cursor placed.tape
  have firstRun:=MixedWriteRuns.trace_run_eq mode (prefix_trace mode layout candidate ruleOld targetOld fresh capacity state entry intact)
  have secondRun:=MixedWriteRuns.trace_run_eq mode (Listing8LiteralMaskTrace.trace mode layout capacity masks _ prefixPC
    (prefix_distribution_current mode layout candidate ruleOld targetOld fresh capacity state entry intact))
  rw [Listing8LiteralComposition.program,MixedWriteRuns.owned_run_append,MixedWriteRuns.owned_run_append,MixedWriteRuns.run_append,firstRun]
  rw [secondRun]
  exact ⟨⟨first,second⟩,third⟩

theorem canonical_owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (placed : Placement mode codeStart codeEnd layout)
    (candidate ruleOld targetOld fresh : Dword) (capacity : endPC mode layout<2^(8*mode.wordBytes))
    (masks : Listing8LiteralMaskTrace.Valid mode layout) (update : InputUpdate.Valid mode (updateLayout mode layout))
    (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    StringWrites.OwnedRun mode codeStart codeEnd
      (((Listing8LiteralComposition.program mode layout candidate ruleOld fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  StringMixedWrites.owned_run mode codeStart codeEnd _ state
    (owned mode codeStart codeEnd layout placed candidate ruleOld targetOld fresh capacity masks update outside state.principal entry intact cursor)

/-- The printed force mask is removed by the actual first reset instruction.
State equality after that instruction transfers the complete remaining run. -/
theorem mask_owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (placed : Placement mode codeStart codeEnd layout)
    (rule tape pending fresh oldMask : Dword) (capacity : endPC mode layout<2^(8*mode.wordBytes))
    (masks : Listing8LiteralMaskTrace.Valid mode layout) (update : InputUpdate.Valid mode (updateLayout mode layout))
    (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    MixedDword.OwnedRun mode (fun address width => codeStart≤address ∧ address+width≤codeEnd)
      (Listing8LiteralComposition.program mode layout rule tape fresh) state := by
  have zero:=Listing8InputMask.zero_intact mode layout rule tape pending fresh oldMask state.memory current
  have cursorFrame:=Listing8LiteralComposition.cursor_field_frame mode layout outside (maskField mode layout)
    (Listing8LiteralComposition.field_bounds mode layout).2.1 state.memory 0
  have fromZero:=owned mode codeStart codeEnd layout placed rule tape pending fresh capacity masks update outside
    (Listing8InputMask.normalized mode layout state) entry zero (cursorFrame.trans cursor)
  constructor
  · exact fromZero.1
  · change MixedDword.OwnedRun mode _ _ (resetState mode layout state)
    rw [Listing8InputMask.reset_same mode layout capacity state entry]
    exact fromZero.2

theorem mask_canonical_owned (mode : Mode) (codeStart codeEnd : Nat) (layout : Layout) (placed : Placement mode codeStart codeEnd layout)
    (rule tape pending fresh oldMask : Dword) (capacity : endPC mode layout<2^(8*mode.wordBytes))
    (masks : Listing8LiteralMaskTrace.Valid mode layout) (update : InputUpdate.Valid mode (updateLayout mode layout))
    (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.principal.memory)
    (cursor : MixedMemory.getWord mode state.principal.memory layout.cursor=Arithmetic.encodeNat mode layout.head) :
    StringWrites.OwnedRun mode codeStart codeEnd
      (((Listing8LiteralComposition.program mode layout rule tape fresh).map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  StringMixedWrites.owned_run mode codeStart codeEnd _ state
    (mask_owned mode codeStart codeEnd layout placed rule tape pending fresh oldMask capacity masks update outside state.principal entry current cursor)

end SmcTuring.Appendix.Listing8LiteralInputWrites

module
public import SmcTuring.Native.MixedFieldOwnership
public import SmcTuring.Appendix.Listing8LiteralInputWrites

public section
namespace SmcTuring.Appendix.Listing8InputTemplateRegions
open Native Listing8LiteralInput

/-- Static ownership of the complete actual fields used by the literal
input phase. No later native state or ownership run is a field. -/
structure Fields (mode : Mode) (layout : Layout) (owned : Nat → Nat → Prop) : Prop where
  scalar : owned (scalarField mode layout) 4
  symbol : owned (sourceField mode layout) 4
  mask : owned (maskField mode layout) 4
  pending : owned (pendingField mode layout) 4
  cursor : owned layout.cursor mode.wordBytes
  tape : owned (layout.head+6) 4
  destinations : ∀ helper∈distributionLayouts mode layout,owned helper.destination 4

theorem comparison (mode : Mode) (layout : DwordComparisonTail.Layout) (valid : DwordComparisonTail.Valid mode layout)
    (symbol : Dword) (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode (layout.start+10))
    (owned : Nat → Nat → Prop) (scalar : owned layout.scalar 4) (mask : owned layout.mask 4) :
    MixedDword.OwnedRun mode owned (DwordComparisonTail.program mode layout symbol) state := by
  have instruction (index : Fin 4) (current : Execution.State mode)
      (located : current.pc=Arithmetic.encodeNat mode (layout.start+DwordComparisonTail.offset index)) :
      owned (MixedDword.address mode (.arithmetic (DwordComparisonTail.form mode layout symbol index)) current).toNat 4 := by
    have fits : DwordComparisonTail.target layout index<2^(8*mode.wordBytes) := by
      have a := valid.scalarFits;have b := valid.maskFits
      fin_cases index <;> simp only [DwordComparisonTail.target] <;> omega
    apply MixedFieldOwnership.located mode _ _ (DwordComparisonTail.raw symbol index) current
      (by fin_cases index <;> rfl) located
      (by have reach := valid.ranges index;fin_cases index <;> exact reach) fits owned
    fin_cases index <;> first | exact scalar | exact mask
  have a := instruction 0 state entry
  have b := instruction 1 (DwordComparisonTail.subState mode layout symbol state)
    (DwordComparisonTail.sub_pc mode layout valid symbol state entry)
  have c := instruction 2 (DwordComparisonTail.negState mode layout symbol state)
    (DwordComparisonTail.neg_pc mode layout valid symbol state entry)
  have d := instruction 3 (DwordComparisonTail.sbbState mode layout symbol state)
    (DwordComparisonTail.sbb_pc mode layout valid symbol state entry)
  exact ⟨a,b,c,d,True.intro⟩

theorem prefix_owned (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (state : Execution.State mode)
    (entry : state.pc=Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (owned : Nat → Nat → Prop) (fields : Fields mode layout owned) :
    MixedDword.OwnedRun mode owned (prefixProgram mode layout candidate ruleOld) state := by
  have valid := tail_valid mode layout capacity
  have scalarFits := valid.scalarFits;have maskFits := valid.maskFits
  simp only [tailLayout] at scalarFits maskFits
  have a := MixedFieldOwnership.located mode layout.start (maskField mode layout) (.store 0 0) state rfl entry
    (by intro long;subst mode;simp [maskField,updateStart,distributionStart,ownerPC,copyStart,gap,DwordLayout.span,
      DwordLayout.storeSize,DwordArithmetic.length,Relocation.SignedDelta,Relocation.delta];omega)
    (by omega) owned fields.mask
  have resetPC : (resetState mode layout state).pc=Arithmetic.encodeNat mode (copyLayout mode layout).start := by
    rw [reset_effect mode layout capacity state entry];rfl
  have b := MixedFieldOwnership.copy mode (copyLayout mode layout) (copy_admissible mode layout capacity)
    (resetState mode layout state) resetPC owned fields.symbol fields.pending
  have copyPC : (copiedState mode layout state).pc=Arithmetic.encodeNat mode (ownerPC mode layout) := by
    rw [copied_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have c := MixedFieldOwnership.located mode (ownerPC mode layout) (scalarField mode layout) (.store 0 candidate)
    (copiedState mode layout state) rfl copyPC
    (by intro long;simpa only [scalarField,DwordArithmetic.length] using DwordOwner.reach (ownerPC mode layout))
    (by omega) owned fields.scalar
  have ownerEntry : (ownerState mode layout candidate state).pc=Arithmetic.encodeNat mode ((tailLayout mode layout).start+10) := by
    rw [owner_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact];rfl
  have d := comparison mode (tailLayout mode layout) valid ruleOld (ownerState mode layout candidate state)
    ownerEntry owned fields.scalar fields.mask
  exact ⟨a,b.1,b.2.1,b.2.2.1,c,d.1,d.2.1,d.2.2.1,d.2.2.2.1,True.intro⟩

/-- The actual equality prefix, every mask-copy helper and the whole cursor
update derive their own store destinations from the original image. -/
theorem complete (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor=Arithmetic.encodeNat mode layout.head)
    (owned : Nat → Nat → Prop) (fields : Fields mode layout owned) :
    MixedDword.OwnedRun mode owned (Listing8LiteralComposition.program mode layout candidate ruleOld fresh) state := by
  have first := prefix_owned mode layout candidate ruleOld targetOld fresh capacity state entry intact owned fields
  have prefixPC := prefix_pc mode layout candidate ruleOld targetOld fresh capacity state entry intact
  have second := MixedFieldOwnership.sequence mode (distributionLayouts mode layout) _
    (Listing8LiteralMaskTrace.chain mode layout) (Listing8LiteralMaskTrace.copies_valid mode layout capacity masks)
    owned (by intro helper member;rw [(Listing8LiteralMaskTrace.helper_bounds mode layout helper member).2.2]
              exact ⟨fields.mask,fields.destinations helper member⟩)
    (prefixState mode layout candidate ruleOld state) prefixPC
  have third := InputUpdateTrace.pure mode (updateLayout mode layout) update ruleOld fresh (chosen candidate ruleOld)
    (Listing8LiteralComposition.distributedState mode layout candidate ruleOld state)
    (Listing8LiteralComposition.distribution_pc mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
    (Listing8LiteralComposition.distribution_update_intact mode layout candidate ruleOld targetOld fresh capacity masks state entry intact)
    ((Listing8LiteralComposition.distribution_cursor mode layout candidate ruleOld targetOld fresh capacity masks outside state entry intact).trans cursor)
    owned fields.pending fields.cursor fields.tape
  have firstRun := MixedWriteRuns.trace_run_eq mode (prefix_trace mode layout candidate ruleOld targetOld fresh capacity state entry intact)
  have secondRun := MixedWriteRuns.trace_run_eq mode (Listing8LiteralMaskTrace.trace mode layout capacity masks _ prefixPC
    (prefix_distribution_current mode layout candidate ruleOld targetOld fresh capacity state entry intact))
  rw [Listing8LiteralComposition.program,MixedWriteRuns.owned_run_append,MixedWriteRuns.owned_run_append,MixedWriteRuns.run_append,firstRun,secondRun]
  exact ⟨⟨first,second⟩,third⟩

theorem mask_complete (mode : Mode) (layout : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode layout<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode layout)
    (update : InputUpdate.Valid mode (updateLayout mode layout)) (outside : Listing8LiteralComposition.DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode layout.start)
    (current : Listing8InputMask.Intact mode layout rule tape pending fresh oldMask state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor=Arithmetic.encodeNat mode layout.head)
    (owned : Nat → Nat → Prop) (fields : Fields mode layout owned) :
    MixedDword.OwnedRun mode owned (Listing8LiteralComposition.program mode layout rule tape fresh) state := by
  have zero := Listing8InputMask.zero_intact mode layout rule tape pending fresh oldMask state.memory current
  have frame := Listing8LiteralComposition.cursor_field_frame mode layout outside (maskField mode layout)
    (Listing8LiteralComposition.field_bounds mode layout).2.1 state.memory 0
  have normalized := complete mode layout rule tape pending fresh capacity masks update outside
    (Listing8InputMask.normalized mode layout state) entry zero (frame.trans cursor) owned fields
  constructor
  · exact normalized.1
  · change MixedDword.OwnedRun mode owned _ (resetState mode layout state)
    rw [Listing8InputMask.reset_same mode layout capacity state entry]
    exact normalized.2

end SmcTuring.Appendix.Listing8InputTemplateRegions

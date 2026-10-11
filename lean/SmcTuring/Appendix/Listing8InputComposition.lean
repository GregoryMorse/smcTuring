module
public import SmcTuring.Appendix.Listing8InputPrefix

public section
namespace SmcTuring.Appendix.Listing8InputComposition
/- This module proves the contiguous prefix/update extraction. The printed
Listing 8 also runs two USEWORDOP64 mask-copy calls between NOT and the update;
their literal placement is not represented by this module's offsets. -/
open Native Listing8InputPrefix
abbrev Dword := BitVec 32

/-- The initial whole Listing 8 image contains the unpatched update body
at the exact endpoint of the nine-instruction prefix. -/
theorem initial_update_intact (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword) (memory : ByteMemory.Memory)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh memory) :
    InputUpdate.Intact mode (updateLayout mode layout) targetOld fresh false memory := by
  have found := ByteWindow.packet memory layout.start
    (prefixBytes mode layout candidate ruleOld)
    (InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false) []
    (by simpa only [Listing8InputPrefix.Intact,bytes,List.length_append,
      List.length_nil,List.append_nil] using intact)
  have position := prefix_length mode layout candidate ruleOld
  simpa only [position,InputUpdate.Intact,InputUpdate.length,updateLayout] using found

/-- The AND immediate is the only varying word in the update image's
second arithmetic packet. -/
theorem update_mask_spelling (mode : Mode) (layout : InputUpdate.Layout)
    (value fresh : Dword) (chosen : Bool) :
    InputUpdate.bytes mode layout value fresh chosen =
      (DwordArithmetic.encode (InputUpdate.xorForm mode layout fresh) ++
        [0x81,0x25] ++
        LittleEndian.wordEncode 4
          (Relocation.memoryDisp mode (layout.start+20) (InputUpdate.field mode layout))) ++
      LittleEndian.wordEncode 4 (InputUpdate.mask chosen) ++
      CursorImage.bytes mode (InputUpdate.body layout) value := by
  simp only [InputUpdate.bytes,InputUpdate.andForm,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length,DwordArithmetic.encode,
    List.append_assoc]

theorem update_mask_patch (mode : Mode) (layout : InputUpdate.Layout)
    (value fresh : Dword) (oldChosen newChosen : Bool)
    (memory : ByteMemory.Memory)
    (intact : InputUpdate.Intact mode layout value fresh oldChosen memory) :
    InputUpdate.Intact mode layout value fresh newChosen
      (DwordCode.put memory (layout.start+16) (InputUpdate.mask newChosen)) := by
  let leading := DwordArithmetic.encode (InputUpdate.xorForm mode layout fresh) ++
    [0x81,0x25] ++
    LittleEndian.wordEncode 4
      (Relocation.memoryDisp mode (layout.start+20) (InputUpdate.field mode layout))
  let trailing := CursorImage.bytes mode (InputUpdate.body layout) value
  have spelling (chosen : Bool) : InputUpdate.bytes mode layout value fresh chosen =
      leading ++ LittleEndian.wordEncode 4 (InputUpdate.mask chosen) ++ trailing :=
    update_mask_spelling mode layout value fresh chosen
  have initial : ByteMemory.bytesAt memory layout.start
      (leading ++ LittleEndian.wordEncode 4 (InputUpdate.mask oldChosen) ++ trailing).length =
      leading ++ LittleEndian.wordEncode 4 (InputUpdate.mask oldChosen) ++ trailing := by
    rw [←spelling,InputUpdate.length]
    exact intact
  have patched := BytePatch.current memory layout.start leading
    (LittleEndian.wordEncode 4 (InputUpdate.mask oldChosen))
    (LittleEndian.wordEncode 4 (InputUpdate.mask newChosen)) trailing
    (by simp only [LittleEndian.word_encode_length]) initial
  have position : layout.start + leading.length = layout.start+16 := by
    simp only [leading,List.length_append,DwordArithmetic.encode_length,
      InputUpdate.xorForm,DwordArithmetic.located,DwordArithmetic.relocate,
      DwordArithmetic.length,LittleEndian.word_encode_length,List.length_cons,
      List.length_nil]
  rw [position,←spelling,InputUpdate.length] at patched
  exact patched

/-- The scalar owner precedes the complete update fragment in the printed
layout, so subsequent scalar writes preserve its image. -/
theorem scalar_before_update (mode : Mode) (layout : Layout) :
    scalarField mode layout + 4 ≤ updateStart mode layout := by
  have ⟨_,scalar,_,_,update,_,_,_⟩ := positions mode layout
  rw [scalar,update]
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega

theorem scalar_update_frame (mode : Mode) (layout : Layout)
    (value fresh : Dword) (chosen : Bool) (memory : ByteMemory.Memory)
    (intact : InputUpdate.Intact mode (updateLayout mode layout) value fresh chosen memory)
    (newScalar : Dword) :
    InputUpdate.Intact mode (updateLayout mode layout) value fresh chosen
      (DwordCode.put memory (scalarField mode layout) newScalar) := by
  apply InputUpdate.intact_external mode (updateLayout mode layout)
    value fresh chosen memory intact
  left
  exact scalar_before_update mode layout

@[expose] def resetState (mode : Mode) (layout : Layout)
    (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (.arithmetic (resetForm mode layout)) state
@[expose] def copiedState (mode : Mode) (layout : Layout)
    (state : Execution.State mode) : Execution.State mode :=
  DwordEffects.finish mode (copyLayout mode layout) (resetState mode layout state)
@[expose] def ownerState (mode : Mode) (layout : Layout) (candidate : Dword)
    (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate))
    (copiedState mode layout state)
@[expose] def subState (mode : Mode) (layout : Layout) (candidate ruleOld : Dword)
    (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld))
    (ownerState mode layout candidate state)
@[expose] def negState (mode : Mode) (layout : Layout) (candidate ruleOld : Dword)
    (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (.arithmetic (negForm mode layout))
    (subState mode layout candidate ruleOld state)
@[expose] def sbbState (mode : Mode) (layout : Layout) (candidate ruleOld : Dword)
    (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (.arithmetic (sbbForm mode layout))
    (negState mode layout candidate ruleOld state)
@[expose] def prefixState (mode : Mode) (layout : Layout) (candidate ruleOld : Dword)
    (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (.arithmetic (notForm mode layout))
    (sbbState mode layout candidate ruleOld state)

@[expose] def mismatch (candidate ruleOld : Dword) : Bool :=
  decide (candidate-ruleOld ≠ 0)
@[expose] def chosen (candidate ruleOld : Dword) : Bool :=
  !mismatch candidate ruleOld

theorem reset_update_intact (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    InputUpdate.Intact mode (updateLayout mode layout) targetOld fresh false
      (resetState mode layout state).memory := by
  rw [resetState,reset_effect mode layout capacity state entry]
  change InputUpdate.Intact mode (updateLayout mode layout) targetOld fresh false
    (DwordCode.put state.memory (maskField mode layout) 0)
  exact update_mask_patch mode (updateLayout mode layout) targetOld fresh false false
    state.memory (initial_update_intact mode layout candidate ruleOld targetOld fresh state.memory intact)

theorem copied_update_intact (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh false
      (copiedState mode layout state).memory := by
  dsimp only [copiedState,resetState]
  rw [reset_copy_exact mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh false
    (DwordCode.put (DwordCode.put state.memory (maskField mode layout) 0)
      (pendingField mode layout) ruleOld)
  exact InputUpdate.patch mode (updateLayout mode layout) targetOld ruleOld fresh false
    (DwordCode.put state.memory (maskField mode layout) 0)
    (update_mask_patch mode (updateLayout mode layout) targetOld fresh false false
      state.memory (initial_update_intact mode layout candidate ruleOld targetOld fresh state.memory intact))

theorem owner_update_intact (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh false
      (ownerState mode layout candidate state).memory := by
  dsimp only [ownerState,copiedState,resetState]
  rw [owner_effect_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  exact copied_update_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact

theorem sub_update_intact (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh false
      (subState mode layout candidate ruleOld state).memory := by
  dsimp only [subState,ownerState,copiedState,resetState]
  rw [sub_effect_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh false
    (DwordCode.put (ownerState mode layout candidate state).memory (scalarField mode layout)
      (candidate-ruleOld))
  exact scalar_update_frame mode layout ruleOld fresh false _
    (owner_update_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact) _

theorem neg_update_intact (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh false
      (negState mode layout candidate ruleOld state).memory := by
  dsimp only [negState,subState,ownerState,copiedState,resetState]
  rw [neg_effect_after_sub mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh false
    (DwordCode.put (subState mode layout candidate ruleOld state).memory (scalarField mode layout)
      (-(candidate-ruleOld)))
  exact scalar_update_frame mode layout ruleOld fresh false _
    (sub_update_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact) _

theorem mask_eq (condition : Bool) :
    InputUpdate.mask condition = BranchAlgebra.mask condition := by
  cases condition <;> rfl

theorem sbb_update_intact (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh
      (mismatch candidate ruleOld) (sbbState mode layout candidate ruleOld state).memory := by
  dsimp only [sbbState,negState,subState,ownerState,copiedState,resetState]
  rw [sbb_effect_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh
    (mismatch candidate ruleOld)
    (DwordCode.put (negState mode layout candidate ruleOld state).memory (maskField mode layout)
      ((0#32) - (if candidate-ruleOld ≠ 0 then 1 else 0)))
  rw [sbb_mask_prop (candidate-ruleOld ≠ 0)]
  simpa only [mask_eq,mismatch,maskField,updateLayout] using
    (update_mask_patch mode (updateLayout mode layout) ruleOld fresh false
      (mismatch candidate ruleOld) _
      (neg_update_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact))

theorem prefix_update_intact (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh
      (chosen candidate ruleOld) (prefixState mode layout candidate ruleOld state).memory := by
  dsimp only [prefixState,sbbState,negState,subState,ownerState,copiedState,resetState]
  rw [not_effect_after_sbb mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh
    (chosen candidate ruleOld)
    (DwordCode.put (sbbState mode layout candidate ruleOld state).memory (maskField mode layout)
      (BranchAlgebra.mask (!(decide (candidate-ruleOld ≠ 0)))))
  simpa only [mask_eq,chosen,mismatch,maskField,updateLayout] using
    (update_mask_patch mode (updateLayout mode layout) ruleOld fresh
      (mismatch candidate ruleOld) (chosen candidate ruleOld) _
    (sbb_update_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact))

theorem prefix_pc (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    (prefixState mode layout candidate ruleOld state).pc =
      Arithmetic.encodeNat mode (updateStart mode layout) := by
  dsimp only [prefixState,sbbState,negState,subState,ownerState,copiedState,resetState]
  rw [not_effect_after_sbb mode layout candidate ruleOld targetOld fresh capacity state entry intact]

theorem prefix_pending (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get (prefixState mode layout candidate ruleOld state).memory
      (pendingField mode layout) = ruleOld := by
  exact InputUpdate.operand mode (updateLayout mode layout) ruleOld fresh
    (chosen candidate ruleOld) _
    (prefix_update_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact)

theorem prefix_mask (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get (prefixState mode layout candidate ruleOld state).memory
      (maskField mode layout) = InputUpdate.mask (chosen candidate ruleOld) := by
  dsimp only [prefixState,sbbState,negState,subState,ownerState,copiedState,resetState]
  rw [not_effect_after_sbb mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  simp only [DwordCode.get_put]
  rw [mask_eq]
  rfl

theorem chosen_iff (candidate ruleOld : Dword) :
    chosen candidate ruleOld = true ↔ candidate = ruleOld := by
  by_cases same : candidate = ruleOld
  · simp [same,chosen,mismatch]
  · have different : candidate-ruleOld ≠ 0 := by
      intro zero
      exact same ((DwordComparison.difference_zero candidate ruleOld).mp zero)
    simp [same,chosen,mismatch]
    exact different

theorem chosen_matches_tape (candidate ruleOld tapeOld : Dword)
    (candidate_is_tape : candidate = tapeOld) :
    chosen candidate ruleOld = true → ruleOld = tapeOld := by
  intro picked
  have same := (chosen_iff candidate ruleOld).mp picked
  rw [←candidate_is_tape]
  exact same.symm

/-- Code and the externally initialized cursor/tape node occupy disjoint
byte ranges; the literal interpreter's actual placement must supply this. -/
structure DataOutside (mode : Mode) (layout : Layout) : Prop where
  cursor : layout.cursor + mode.wordBytes ≤ layout.start ∨ endPC mode layout ≤ layout.cursor
  tape : layout.head + 10 ≤ layout.start ∨ endPC mode layout ≤ layout.head + 6

theorem code_field_bounds (mode : Mode) (layout : Layout) :
    (layout.start ≤ scalarField mode layout ∧ scalarField mode layout + 4 ≤ endPC mode layout) ∧
    (layout.start ≤ maskField mode layout ∧ maskField mode layout + 4 ≤ endPC mode layout) ∧
    (layout.start ≤ pendingField mode layout ∧ pendingField mode layout + 4 ≤ endPC mode layout) := by
  have ⟨_,scalar,_,_,_,mask,pending,ending⟩ := positions mode layout
  rw [scalar,mask,pending,ending]
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega

theorem cursor_field_frame (mode : Mode) (layout : Layout)
    (outside : DataOutside mode layout) (field : Nat)
    (within : layout.start ≤ field ∧ field + 4 ≤ endPC mode layout)
    (memory : ByteMemory.Memory) (value : Dword) :
    MixedMemory.getWord mode (DwordCode.put memory field value) layout.cursor =
      MixedMemory.getWord mode memory layout.cursor := by
  apply MixedMemory.wide_after_dword
  intro index
  have bound := index.isLt
  simp only [ByteMemory.Inside]
  rcases outside.cursor with before | after <;> omega

theorem tape_field_frame (mode : Mode) (layout : Layout)
    (outside : DataOutside mode layout) (field : Nat)
    (within : layout.start ≤ field ∧ field + 4 ≤ endPC mode layout)
    (memory : ByteMemory.Memory) (value : Dword) :
    DwordCode.get (DwordCode.put memory field value) (layout.head+6) =
      DwordCode.get memory (layout.head+6) := by
  apply DwordCode.get_frame
  intro index
  have bound := index.isLt
  simp only [ByteMemory.Inside]
  rcases outside.tape with before | after <;> omega

@[expose] def prefixMemory (mode : Mode) (layout : Layout)
    (candidate ruleOld : Dword) (memory : ByteMemory.Memory) : ByteMemory.Memory :=
  DwordCode.put
    (DwordCode.put
      (DwordCode.put
        (DwordCode.put
          (DwordCode.put
            (DwordCode.put memory (maskField mode layout) 0)
              (pendingField mode layout) ruleOld)
            (scalarField mode layout) (candidate-ruleOld))
          (scalarField mode layout) (-(candidate-ruleOld)))
        (maskField mode layout)
        ((0#32) - (if candidate-ruleOld ≠ 0 then 1 else 0)))
      (maskField mode layout)
      (BranchAlgebra.mask (chosen candidate ruleOld))

theorem prefix_memory (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    (prefixState mode layout candidate ruleOld state).memory =
      prefixMemory mode layout candidate ruleOld state.memory := by
  dsimp only [prefixState,sbbState,negState,subState,ownerState,copiedState,resetState]
  rw [not_effect_after_sbb mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    sbb_effect_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    neg_effect_after_sub mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    sub_effect_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    owner_effect_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    reset_copy_exact mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  rfl

theorem prefix_cursor (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    MixedMemory.getWord mode (prefixState mode layout candidate ruleOld state).memory layout.cursor =
      MixedMemory.getWord mode state.memory layout.cursor := by
  rw [prefix_memory mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  simp only [prefixMemory]
  have ⟨scalar,mask,pending⟩ := code_field_bounds mode layout
  rw [cursor_field_frame mode layout outside _ mask,
    cursor_field_frame mode layout outside _ mask,
    cursor_field_frame mode layout outside _ scalar,
    cursor_field_frame mode layout outside _ scalar,
    cursor_field_frame mode layout outside _ pending,
    cursor_field_frame mode layout outside _ mask]

theorem prefix_tape (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get (prefixState mode layout candidate ruleOld state).memory (layout.head+6) =
      DwordCode.get state.memory (layout.head+6) := by
  rw [prefix_memory mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  simp only [prefixMemory]
  have ⟨scalar,mask,pending⟩ := code_field_bounds mode layout
  rw [tape_field_frame mode layout outside _ mask,
    tape_field_frame mode layout outside _ mask,
    tape_field_frame mode layout outside _ scalar,
    tape_field_frame mode layout outside _ scalar,
    tape_field_frame mode layout outside _ pending,
    tape_field_frame mode layout outside _ mask]

/-- All fourteen instructions in the contiguous prefix/update extraction fetch
their current bytes from one initialized image. The printed mask-copy gap must
still be inserted for the literal whole Listing 8 trace. -/
theorem full_input_trace (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (valid : InputUpdate.Valid mode (updateLayout mode layout))
    (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor =
      Arithmetic.encodeNat mode layout.head) :
    MixedDword.Trace mode state
      (prefixProgram mode layout candidate ruleOld ++
        InputUpdate.program mode (updateLayout mode layout) ruleOld fresh
          (chosen candidate ruleOld))
      (InputUpdate.finish mode (updateLayout mode layout) ruleOld fresh
        (chosen candidate ruleOld) (prefixState mode layout candidate ruleOld state)) := by
  have first : MixedDword.Trace mode state (prefixProgram mode layout candidate ruleOld)
      (prefixState mode layout candidate ruleOld state) := by
    simpa only [prefixState,sbbState,negState,subState,ownerState,copiedState,resetState]
      using Listing8InputPrefix.prefix_trace mode layout candidate ruleOld targetOld fresh
        capacity state entry intact
  have liveCursor : MixedMemory.getWord mode
      (prefixState mode layout candidate ruleOld state).memory layout.cursor =
      Arithmetic.encodeNat mode layout.head :=
    (prefix_cursor mode layout candidate ruleOld targetOld fresh capacity outside state entry intact).trans cursor
  have second := InputUpdateTrace.trace mode (updateLayout mode layout) valid ruleOld fresh
    (chosen candidate ruleOld) (prefixState mode layout candidate ruleOld state)
    (prefix_pc mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    (prefix_update_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    liveCursor
  exact MixedDword.trace_append mode first second

/-- The complete selected input effect uses the comparison result to connect
the copied rule symbol with the live tape symbol on the chosen path. -/
theorem full_input_effect (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (valid : InputUpdate.Valid mode (updateLayout mode layout))
    (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor =
      Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = candidate) :
    InputUpdate.finish mode (updateLayout mode layout) ruleOld fresh
      (chosen candidate ruleOld) (prefixState mode layout candidate ruleOld state) =
      { prefixState mode layout candidate ruleOld state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        carry := false
        memory := DwordCode.put
          (DwordCode.put (prefixState mode layout candidate ruleOld state).memory
            (pendingField mode layout)
            (CursorEffects.delta ruleOld fresh (chosen candidate ruleOld)))
          (layout.head+6) (if chosen candidate ruleOld then fresh else candidate) } := by
  have liveCursor : MixedMemory.getWord mode
      (prefixState mode layout candidate ruleOld state).memory layout.cursor =
      Arithmetic.encodeNat mode layout.head :=
    (prefix_cursor mode layout candidate ruleOld targetOld fresh capacity outside state entry intact).trans cursor
  have liveTape : DwordCode.get (prefixState mode layout candidate ruleOld state).memory
      (layout.head+6) = candidate :=
    (prefix_tape mode layout candidate ruleOld targetOld fresh capacity outside state entry intact).trans tape
  have result := InputUpdateTrace.effect_rule mode (updateLayout mode layout) valid
    ruleOld candidate fresh (chosen candidate ruleOld)
    (prefixState mode layout candidate ruleOld state)
    (prefix_pc mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    (prefix_update_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    liveCursor liveTape (chosen_matches_tape candidate ruleOld candidate rfl)
  have endpoint : CursorLayout.endPC mode (InputUpdate.body (updateLayout mode layout)) =
      endPC mode layout := by
    rw [InputUpdate.endpoint]
    rfl
  rw [endpoint] at result
  exact result

/-- The update's live code image is retained for the next interpreter step,
with its pending immediate changed to the just-computed XOR delta. -/
theorem full_input_retained (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (valid : InputUpdate.Valid mode (updateLayout mode layout))
    (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor =
      Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = candidate) :
    InputUpdate.Intact mode (updateLayout mode layout)
      (CursorEffects.delta ruleOld fresh (chosen candidate ruleOld)) fresh
      (chosen candidate ruleOld)
      (InputUpdate.finish mode (updateLayout mode layout) ruleOld fresh
        (chosen candidate ruleOld) (prefixState mode layout candidate ruleOld state)).memory := by
  have liveCursor : MixedMemory.getWord mode
      (prefixState mode layout candidate ruleOld state).memory layout.cursor =
      Arithmetic.encodeNat mode layout.head :=
    (prefix_cursor mode layout candidate ruleOld targetOld fresh capacity outside state entry intact).trans cursor
  have liveTape : DwordCode.get (prefixState mode layout candidate ruleOld state).memory
      (layout.head+6) = candidate :=
    (prefix_tape mode layout candidate ruleOld targetOld fresh capacity outside state entry intact).trans tape
  exact InputUpdateTrace.retained_image_rule mode (updateLayout mode layout) valid
    ruleOld candidate fresh (chosen candidate ruleOld)
    (prefixState mode layout candidate ruleOld state)
    (prefix_pc mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    (prefix_update_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    liveCursor liveTape (chosen_matches_tape candidate ruleOld candidate rfl)

theorem full_input_tape (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (valid : InputUpdate.Valid mode (updateLayout mode layout))
    (outside : DataOutside mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Listing8InputPrefix.Intact mode layout candidate ruleOld targetOld fresh state.memory)
    (cursor : MixedMemory.getWord mode state.memory layout.cursor =
      Arithmetic.encodeNat mode layout.head)
    (tape : DwordCode.get state.memory (layout.head+6) = candidate) :
    DwordCode.get
      (InputUpdate.finish mode (updateLayout mode layout) ruleOld fresh
        (chosen candidate ruleOld) (prefixState mode layout candidate ruleOld state)).memory
      (layout.head+6) = if chosen candidate ruleOld then fresh else candidate := by
  rw [full_input_effect mode layout candidate ruleOld targetOld fresh capacity valid outside
    state entry intact cursor tape]
  exact DwordCode.get_put _ _ _

end SmcTuring.Appendix.Listing8InputComposition

module
public import SmcTuring.Appendix.DwordComparisonTail
public import SmcTuring.Appendix.Listing8MaskCopy
public import SmcTuring.Appendix.Listing8InputComposition
public import SmcTuring.Native.DwordMixedImage

public section
namespace SmcTuring.Appendix.Listing8LiteralInput
open Native
abbrev Dword := BitVec 32

/-- The two destination masks are live immediates in the later transition
and direction code. Their full interpreter placement is caller work. -/
structure Layout where
  start : Nat
  cursor : Nat
  head : Nat
  transitionMask : Nat
  directionMask : Nat

@[expose] def copyStart (layout : Layout) := layout.start+10
@[expose] def ownerPC (mode : Mode) (layout : Layout) := copyStart layout+DwordLayout.span mode
@[expose] def distributionStart (mode : Mode) (layout : Layout) := ownerPC mode layout+39
@[expose] def gap (mode : Mode) := if mode = .x86 then 34 else 72
@[expose] def updateStart (mode : Mode) (layout : Layout) := distributionStart mode layout+gap mode
@[expose] def updateLayout (mode : Mode) (layout : Layout) : InputUpdate.Layout :=
  { start := updateStart mode layout, cursor := layout.cursor, head := layout.head }
@[expose] def scalarField (mode : Mode) (layout : Layout) := ownerPC mode layout+6
@[expose] def sourceField (mode : Mode) (layout : Layout) := ownerPC mode layout+16
@[expose] def maskField (mode : Mode) (layout : Layout) := updateStart mode layout+16
@[expose] def pendingField (mode : Mode) (layout : Layout) := InputUpdate.field mode (updateLayout mode layout)
@[expose] def endPC (mode : Mode) (layout : Layout) := updateStart mode layout+InputUpdate.span mode
@[expose] def copyLayout (mode : Mode) (layout : Layout) : DwordLayout.Layout :=
  { start := copyStart layout, source := sourceField mode layout, destination := pendingField mode layout }
@[expose] def tailLayout (mode : Mode) (layout : Layout) : DwordComparisonTail.Layout :=
  { start := ownerPC mode layout, scalar := scalarField mode layout, mask := maskField mode layout }
@[expose] def resetForm (mode : Mode) (layout : Layout) : DwordArithmetic.Form :=
  DwordArithmetic.located mode (.store 0 0) layout.start (maskField mode layout)
@[expose] def ownerForm (mode : Mode) (layout : Layout) (candidate : Dword) : DwordArithmetic.Form :=
  DwordArithmetic.located mode (.store 0 candidate) (ownerPC mode layout) (scalarField mode layout)
@[expose] def distributionLayouts (mode : Mode) (layout : Layout) :=
  Listing8MaskCopy.distributionLayouts mode (distributionStart mode layout)
    (maskField mode layout) layout.transitionMask layout.directionMask
@[expose] def distributionBytes (mode : Mode) (layout : Layout) :=
  Listing8MaskCopy.distributionBytes mode (distributionStart mode layout)
    (maskField mode layout) layout.transitionMask layout.directionMask
@[expose] def prefixBytes (mode : Mode) (layout : Layout) (candidate ruleOld : Dword) :=
  DwordArithmetic.encode (resetForm mode layout) ++ DwordMixedImage.bytes mode (copyLayout mode layout) ++
    DwordArithmetic.encode (ownerForm mode layout candidate) ++
    DwordComparisonTail.bytes mode (tailLayout mode layout) ruleOld
@[expose] def bytes (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword) :=
  prefixBytes mode layout candidate ruleOld ++ distributionBytes mode layout ++
    InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false
@[expose] def Intact (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) : Prop :=
  ByteMemory.bytesAt memory layout.start (bytes mode layout candidate ruleOld targetOld fresh).length =
    bytes mode layout candidate ruleOld targetOld fresh
@[expose] def image (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (backing : ByteMemory.Memory) :=
  ByteMemory.putBytes backing layout.start (bytes mode layout candidate ruleOld targetOld fresh)

theorem positions (mode : Mode) (layout : Layout) :
    ownerPC mode layout = layout.start+(if mode = .x86 then 27 else 28) ∧
    scalarField mode layout = layout.start+(if mode = .x86 then 33 else 34) ∧
    sourceField mode layout = layout.start+(if mode = .x86 then 43 else 44) ∧
    distributionStart mode layout = layout.start+(if mode = .x86 then 66 else 67) ∧
    updateStart mode layout = layout.start+(if mode = .x86 then 100 else 139) ∧
    maskField mode layout = layout.start+(if mode = .x86 then 116 else 155) ∧
    pendingField mode layout = layout.start+(if mode = .x86 then 129 else 169) ∧
    endPC mode layout = layout.start+(if mode = .x86 then 139 else 180) := by
  cases mode <;> simp [ownerPC,copyStart,scalarField,sourceField,distributionStart,updateStart,gap,
    maskField,pendingField,updateLayout,endPC,DwordLayout.span,DwordLayout.storeSize,
    InputUpdate.field,InputUpdate.body,CursorPatch.field,CursorLayout.middlePC,
    CursorLayout.exchangeSize,InputUpdate.span,CursorImage.span,instructionLength,
    MemoryOp.prefix,MemoryOp.trailer,wordPrefix]

theorem prefix_length (mode : Mode) (layout : Layout) (candidate ruleOld : Dword) :
    layout.start+(prefixBytes mode layout candidate ruleOld).length = distributionStart mode layout := by
  simp only [prefixBytes,List.length_append,DwordMixedImage.bytes_length,DwordComparisonTail.length,
    resetForm,ownerForm,DwordArithmetic.encode_length,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length]
  unfold distributionStart ownerPC copyStart
  omega

theorem distribution_length (mode : Mode) (layout : Layout) :
    (distributionBytes mode layout).length = gap mode :=
  Listing8MaskCopy.distribution_length mode _ _ _ _

theorem bytes_length (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword) :
    layout.start+(bytes mode layout candidate ruleOld targetOld fresh).length = endPC mode layout := by
  simp only [bytes,List.length_append,distribution_length,InputUpdate.length]
  have hprefix := prefix_length mode layout candidate ruleOld
  unfold endPC updateStart
  omega

theorem initial_intact (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (backing : ByteMemory.Memory) :
    Intact mode layout candidate ruleOld targetOld fresh (image mode layout candidate ruleOld targetOld fresh backing) :=
  ByteMemory.bytes_at_put _ _ _

theorem copy_admissible (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) :
    DwordLayout.Admissible mode (copyLayout mode layout) := by
  cases mode <;> refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp [copyLayout,copyStart,sourceField,ownerPC,pendingField,updateLayout,updateStart,
      distributionStart,gap,endPC,DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,
      DwordLayout.span,DwordLayout.storeSize,InputUpdate.span,CursorImage.span,
      InputUpdate.field,InputUpdate.body,CursorPatch.field,CursorLayout.middlePC,
      CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,
      Relocation.SignedDelta,Relocation.delta] at * <;> omega

theorem tail_valid (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) :
    DwordComparisonTail.Valid mode (tailLayout mode layout) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
  | (intro index long
     subst mode
     fin_cases index <;>
       simp [tailLayout,DwordComparisonTail.offset,DwordComparisonTail.target,DwordComparisonTail.raw,
         DwordArithmetic.length,ownerPC,copyStart,scalarField,maskField,updateStart,distributionStart,gap,
         DwordLayout.span,DwordLayout.storeSize,Relocation.SignedDelta,Relocation.delta] <;> omega)
  | (have coords := positions mode layout
     rcases coords with ⟨owner,scalar,source,dist,update,mask,pending,ending⟩
     simp only [tailLayout] at *
     rw [ending] at capacity
     simp only [owner,scalar,mask]
     cases mode <;> simp only [ite_true,ite_false,reduceCtorEq,Mode.wordBytes] at * <;> omega)

theorem reset_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory layout.start (DwordArithmetic.encode (resetForm mode layout)).length =
      DwordArithmetic.encode (resetForm mode layout) :=
  ByteWindow.packet memory layout.start [] _
    (DwordMixedImage.bytes mode (copyLayout mode layout) ++
      DwordArithmetic.encode (ownerForm mode layout candidate) ++
      DwordComparisonTail.bytes mode (tailLayout mode layout) ruleOld ++ distributionBytes mode layout ++
      InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)

theorem copy_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    DwordImage.Intact mode (copyLayout mode layout) memory := by
  apply DwordMixedImage.intact_of_bytes
  have packet := ByteWindow.packet memory layout.start (DwordArithmetic.encode (resetForm mode layout))
    (DwordMixedImage.bytes mode (copyLayout mode layout))
    (DwordArithmetic.encode (ownerForm mode layout candidate) ++
      DwordComparisonTail.bytes mode (tailLayout mode layout) ruleOld ++ distributionBytes mode layout ++
      InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)
  simpa [copyLayout,copyStart,resetForm,DwordArithmetic.encode_length,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length] using packet

theorem owner_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (ownerPC mode layout) 10 = DwordOwner.bytes mode (ownerPC mode layout) candidate := by
  have packet := ByteWindow.packet memory layout.start
    (DwordArithmetic.encode (resetForm mode layout) ++ DwordMixedImage.bytes mode (copyLayout mode layout))
    (DwordArithmetic.encode (ownerForm mode layout candidate))
    (DwordComparisonTail.bytes mode (tailLayout mode layout) ruleOld ++ distributionBytes mode layout ++
      InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)
  have binding : DwordArithmetic.encode (ownerForm mode layout candidate) =
      DwordOwner.bytes mode (ownerPC mode layout) candidate := by cases mode <;> rfl
  simpa [binding,ownerPC,copyStart,List.length_append,DwordMixedImage.bytes_length,resetForm,
    DwordArithmetic.encode_length,DwordArithmetic.located,DwordArithmetic.relocate,
    DwordArithmetic.length,Nat.add_assoc,DwordOwner.length] using packet

theorem tail_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    DwordComparisonTail.Intact mode (tailLayout mode layout) ruleOld memory := by
  have packet := ByteWindow.packet memory layout.start
    (DwordArithmetic.encode (resetForm mode layout) ++ DwordMixedImage.bytes mode (copyLayout mode layout) ++
      DwordArithmetic.encode (ownerForm mode layout candidate))
    (DwordComparisonTail.bytes mode (tailLayout mode layout) ruleOld)
    (distributionBytes mode layout ++ InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)
  simpa [DwordComparisonTail.Intact,tailLayout,ownerPC,copyStart,List.length_append,
    DwordMixedImage.bytes_length,DwordComparisonTail.length,resetForm,ownerForm,
    DwordArithmetic.encode_length,DwordArithmetic.located,DwordArithmetic.relocate,
    DwordArithmetic.length,Nat.add_assoc] using packet

theorem distribution_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (distributionStart mode layout) (distributionBytes mode layout).length =
      distributionBytes mode layout := by
  have packet := ByteWindow.packet memory layout.start (prefixBytes mode layout candidate ruleOld)
    (distributionBytes mode layout) (InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes] using intact)
  simpa only [prefix_length] using packet

theorem update_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    InputUpdate.Intact mode (updateLayout mode layout) targetOld fresh false memory := by
  have packet := ByteWindow.packet memory layout.start
    (prefixBytes mode layout candidate ruleOld ++ distributionBytes mode layout)
    (InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false) []
    (by simpa [Intact,bytes,List.append_assoc] using intact)
  have position : layout.start+(prefixBytes mode layout candidate ruleOld ++ distributionBytes mode layout).length =
      updateStart mode layout := by
    simp only [List.length_append,distribution_length]
    have hprefix := prefix_length mode layout candidate ruleOld
    unfold updateStart
    omega
  simpa only [position,InputUpdate.length,InputUpdate.Intact,updateLayout] using packet

@[expose] def resetState (mode : Mode) (layout : Layout) (state : Execution.State mode) :=
  DwordArithmetic.execute mode (resetForm mode layout) state
@[expose] def copiedState (mode : Mode) (layout : Layout) (state : Execution.State mode) :=
  DwordEffects.finish mode (copyLayout mode layout) (resetState mode layout state)
@[expose] def ownerState (mode : Mode) (layout : Layout) (candidate : Dword) (state : Execution.State mode) :=
  DwordArithmetic.execute mode (ownerForm mode layout candidate) (copiedState mode layout state)
@[expose] def prefixState (mode : Mode) (layout : Layout) (candidate ruleOld : Dword) (state : Execution.State mode) :=
  DwordComparisonTail.finish mode (tailLayout mode layout) ruleOld (ownerState mode layout candidate state)
@[expose] def chosen (candidate ruleOld : Dword) := !DwordComparisonTail.mismatch candidate ruleOld
@[expose] def prefixProgram (mode : Mode) (layout : Layout) (candidate ruleOld : Dword) :=
  [.arithmetic (resetForm mode layout)] ++
    (DwordLayout.program mode (copyLayout mode layout)).map MixedDword.Form.copy ++
    [.arithmetic (ownerForm mode layout candidate)] ++
    DwordComparisonTail.program mode (tailLayout mode layout) ruleOld

/-- Relevant packed fields are separated from each earlier packet region. -/
theorem field_geometry (mode : Mode) (layout : Layout) :
    scalarField mode layout+4 ≤ distributionStart mode layout ∧
    distributionStart mode layout ≤ maskField mode layout ∧
    distributionStart mode layout ≤ pendingField mode layout ∧
    maskField mode layout+4 ≤ pendingField mode layout ∧
    DwordLayout.endPC mode (copyLayout mode layout) = ownerPC mode layout ∧
    ownerPC mode layout+10 ≤ maskField mode layout ∧
    ownerPC mode layout+10 ≤ pendingField mode layout ∧
    sourceField mode layout+4 ≤ maskField mode layout ∧
    updateStart mode layout ≤ maskField mode layout ∧
    updateStart mode layout ≤ pendingField mode layout := by
  have ⟨owner,scalar,source,dist,update,mask,pending,ending⟩ := positions mode layout
  rw [DwordLayout.endpoint]
  simp only [copyLayout,copyStart,ownerPC] at ⊢
  rw [scalar,dist,mask,pending,source,update]
  cases mode <;> simp [DwordLayout.span,DwordLayout.storeSize] at *

theorem reset_effect (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    resetState mode layout state =
      { state with
        pc := Arithmetic.encodeNat mode (copyStart layout),
        memory := DwordCode.put state.memory (maskField mode layout) 0 } := by
  have range : mode = .x64 → Relocation.SignedDelta (layout.start+10) (maskField mode layout) := by
    intro long
    subst mode
    simp [maskField,updateStart,distributionStart,ownerPC,copyStart,gap,DwordLayout.span,
      DwordLayout.storeSize,Relocation.SignedDelta,Relocation.delta] <;> omega
  have fits := (tail_valid mode layout capacity).maskFits
  have step := DwordArithmetic.located_effect mode (.store 0 0) layout.start (maskField mode layout)
    state rfl entry range (by simp only [tailLayout] at fits; omega)
  simpa [resetState,resetForm,copyStart,DwordArithmetic.flag,DwordArithmetic.result,DwordArithmetic.length] using step

theorem source_value (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    DwordCode.get memory (sourceField mode layout) = ruleOld := by
  have packet := DwordComparisonTail.current_packet mode (tailLayout mode layout) ruleOld memory
    (tail_current mode layout candidate ruleOld targetOld fresh memory intact) 0
  have word := ByteWindow.packet memory (ownerPC mode layout+10)
    ([0x81,0x2d] ++ LittleEndian.wordEncode 4
      (Relocation.memoryDisp mode (ownerPC mode layout+20) (scalarField mode layout)))
    (LittleEndian.wordEncode 4 ruleOld) []
    (by simpa [DwordComparisonTail.form,DwordComparisonTail.raw,DwordComparisonTail.offset,
      DwordComparisonTail.target,tailLayout,DwordArithmetic.located,DwordArithmetic.relocate,
      DwordArithmetic.encode,DwordArithmetic.length,Nat.add_assoc] using packet)
  have bytesAt : ByteMemory.bytesAt memory (sourceField mode layout) 4 = LittleEndian.wordEncode 4 ruleOld := by
    simpa [sourceField,List.length_append,LittleEndian.word_encode_length,Nat.add_assoc] using word
  have decoded : ByteMemory.readWord .x86 memory (sourceField mode layout) = some ruleOld := by
    change LittleEndian.wordDecode 4 (ByteMemory.bytesAt memory (sourceField mode layout) 4) = some ruleOld
    rw [bytesAt,LittleEndian.word_decode_encode]
  rw [DwordCode.read_total] at decoded
  exact Option.some.inj decoded

theorem copied_effect (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    copiedState mode layout state =
      { state with
        pc := Arithmetic.encodeNat mode (ownerPC mode layout),
        accumulator := DwordCode.lift mode (DwordCode.low mode state.accumulator),
        memory := DwordCode.put (DwordCode.put state.memory (maskField mode layout) 0)
          (pendingField mode layout) ruleOld } := by
  have location : (resetState mode layout state).pc = Arithmetic.encodeNat mode (copyLayout mode layout).start := by
    rw [reset_effect mode layout capacity state entry]
    rfl
  rw [copiedState,DwordEffects.effect mode _ (copy_admissible mode layout capacity) _ location,
    reset_effect mode layout capacity state entry,(field_geometry mode layout).2.2.2.2.1]
  have sourceFrame : ∀ index : Fin 4, ¬ByteMemory.Inside (maskField mode layout) 4 (sourceField mode layout+index.val) := by
    intro index
    have bound := index.isLt
    have geometry := field_geometry mode layout
    simp only [ByteMemory.Inside]
    omega
  simp only [copyLayout]
  rw [DwordCode.get_frame _ _ _ _ sourceFrame,source_value mode layout candidate ruleOld targetOld fresh state.memory intact]

theorem owner_after_copy (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    ByteMemory.bytesAt (copiedState mode layout state).memory (ownerPC mode layout) 10 =
      DwordOwner.bytes mode (ownerPC mode layout) candidate := by
  rw [copied_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have geometry := field_geometry mode layout
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by omega)),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by omega))]
  exact owner_current mode layout candidate ruleOld targetOld fresh state.memory intact

theorem owner_effect (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    ownerState mode layout candidate state =
      { copiedState mode layout state with pc := Arithmetic.encodeNat mode (ownerPC mode layout+10) } := by
  have location : (copiedState mode layout state).pc = Arithmetic.encodeNat mode (ownerPC mode layout) := by
    rw [copied_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have fits := (tail_valid mode layout capacity).scalarFits
  have step := DwordArithmetic.located_effect mode (.store 0 candidate) (ownerPC mode layout)
    (scalarField mode layout) (copiedState mode layout state) rfl location
    (by intro long; simpa only [scalarField,DwordArithmetic.length] using DwordOwner.reach (ownerPC mode layout))
    (by simp only [tailLayout] at fits; omega)
  have current := DwordOwner.current_immediate mode (ownerPC mode layout) candidate _
    (owner_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact)
  have unchanged : DwordCode.put (copiedState mode layout state).memory (scalarField mode layout) candidate =
      (copiedState mode layout state).memory := by
    apply ByteMemory.put_current
    simpa only [scalarField,LittleEndian.word_encode_length] using current
  simpa only [ownerState,ownerForm,DwordArithmetic.flag,DwordArithmetic.result,DwordArithmetic.length,unchanged] using step

theorem owner_scalar (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get (ownerState mode layout candidate state).memory (scalarField mode layout) = candidate := by
  rw [owner_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have current := DwordOwner.current_immediate mode (ownerPC mode layout) candidate _
    (owner_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact)
  have decoded : ByteMemory.readWord .x86 (copiedState mode layout state).memory (scalarField mode layout) = some candidate := by
    change LittleEndian.wordDecode 4 (ByteMemory.bytesAt _ (scalarField mode layout) 4) = some candidate
    change ByteMemory.bytesAt _ (scalarField mode layout) 4 = _ at current
    rw [current,LittleEndian.word_decode_encode]
  rw [DwordCode.read_total] at decoded
  exact Option.some.inj decoded

theorem owner_mask (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get (ownerState mode layout candidate state).memory (maskField mode layout) = 0 := by
  rw [owner_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    copied_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  rw [DwordCode.get_frame _ _ _ _ (by
    intro index
    have bound := index.isLt
    have geometry := field_geometry mode layout
    simp only [ByteMemory.Inside]
    omega),DwordCode.get_put]

theorem owner_tail (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordComparisonTail.Intact mode (tailLayout mode layout) ruleOld (ownerState mode layout candidate state).memory := by
  rw [owner_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    copied_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have geometry := field_geometry mode layout
  apply DwordComparisonTail.intact_put
  · apply DwordComparisonTail.intact_put
    · exact tail_current mode layout candidate ruleOld targetOld fresh state.memory intact
    · right
      change distributionStart mode layout ≤ maskField mode layout
      omega
  · right
    change distributionStart mode layout ≤ pendingField mode layout
    omega

/-- The reset and M13/M14 entry facts are derived from one literal image;
the four comparison fetches then follow from the audited relocated tail. -/
theorem prefix_trace (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    MixedDword.Trace mode state (prefixProgram mode layout candidate ruleOld)
      (prefixState mode layout candidate ruleOld state) := by
  have startFits : layout.start < 2^(8*mode.wordBytes) := by
    have coords := (positions mode layout).2.2.2.2.2.2.2
    rw [coords] at capacity
    omega
  have first : MixedDword.Trace mode state [.arithmetic (resetForm mode layout)] (resetState mode layout state) :=
    .step (by rw [entry,Arithmetic.encode_nat_toNat mode _ startFits]
              exact MixedDword.arithmetic_encoding mode _ _ _ (reset_current mode layout candidate ruleOld targetOld fresh state.memory intact)) (.nil _)
  have resetPC : (resetState mode layout state).pc = Arithmetic.encodeNat mode (copyStart layout) := by
    rw [reset_effect mode layout capacity state entry]
  have resetImage : DwordImage.Intact mode (copyLayout mode layout) (resetState mode layout state).memory := by
    rw [reset_effect mode layout capacity state entry]
    apply DwordImage.intact_put _ _ _ (copy_current mode layout candidate ruleOld targetOld fresh state.memory intact)
    right
    have geometry := field_geometry mode layout
    rw [geometry.2.2.2.2.1]
    omega
  have copy := DwordMixedImage.trace mode (copyLayout mode layout) (copy_admissible mode layout capacity) _ resetPC resetImage
  have ownerPCeq : (copiedState mode layout state).pc = Arithmetic.encodeNat mode (ownerPC mode layout) := by
    rw [copied_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have ownerFits : ownerPC mode layout < 2^(8*mode.wordBytes) := by
    have valid := tail_valid mode layout capacity
    have bound := valid.codeFits
    simp only [tailLayout] at bound
    omega
  have ownerPacket := owner_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact
  have binding : DwordArithmetic.encode (ownerForm mode layout candidate) = DwordOwner.bytes mode (ownerPC mode layout) candidate := by cases mode <;> rfl
  have ownerFetch : MixedDword.fetch mode (copiedState mode layout state).memory (copiedState mode layout state).pc.toNat =
      some (.arithmetic (ownerForm mode layout candidate)) := by
    rw [ownerPCeq,Arithmetic.encode_nat_toNat mode _ ownerFits]
    apply MixedDword.arithmetic_encoding
    simpa only [binding,DwordOwner.length] using ownerPacket
  have ownerTrace : MixedDword.Trace mode (copiedState mode layout state)
      [.arithmetic (ownerForm mode layout candidate)] (ownerState mode layout candidate state) := .step ownerFetch (.nil _)
  have tailPC : (ownerState mode layout candidate state).pc = Arithmetic.encodeNat mode ((tailLayout mode layout).start+10) := by
    rw [owner_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
    rfl
  have tail := DwordComparisonTail.trace mode (tailLayout mode layout) (tail_valid mode layout capacity) ruleOld _ tailPC
    (owner_tail mode layout candidate ruleOld targetOld fresh capacity state entry intact)
  exact MixedDword.trace_append mode (MixedDword.trace_append mode (MixedDword.trace_append mode first copy) ownerTrace) tail

theorem prefix_effect (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    prefixState mode layout candidate ruleOld state =
      { state with
        pc := Arithmetic.encodeNat mode (distributionStart mode layout),
        accumulator := DwordCode.lift mode (DwordCode.low mode state.accumulator),
        carry := DwordComparisonTail.mismatch candidate ruleOld,
        memory := DwordCode.put
          (DwordCode.put
            (DwordCode.put (DwordCode.put state.memory (maskField mode layout) 0) (pendingField mode layout) ruleOld)
            (scalarField mode layout) (-(candidate-ruleOld)))
          (maskField mode layout) (InputUpdate.mask (chosen candidate ruleOld)) } := by
  have tailPC : (ownerState mode layout candidate state).pc = Arithmetic.encodeNat mode ((tailLayout mode layout).start+10) := by
    rw [owner_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
    rfl
  rw [prefixState,DwordComparisonTail.effect mode (tailLayout mode layout) (tail_valid mode layout capacity) candidate ruleOld _ tailPC
    (owner_scalar mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    (owner_mask mode layout candidate ruleOld targetOld fresh capacity state entry intact),
    owner_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    copied_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  simp only [tailLayout,distributionStart,chosen,Listing8InputComposition.mask_eq]

theorem prefix_distribution_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    ByteMemory.bytesAt (prefixState mode layout candidate ruleOld state).memory
      (distributionStart mode layout) (distributionBytes mode layout).length = distributionBytes mode layout := by
  rw [prefix_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have geometry := field_geometry mode layout
  have high : distributionStart mode layout+(distributionBytes mode layout).length = updateStart mode layout := by
    rw [distribution_length]
    rfl
  have maskAfter : distributionStart mode layout+(distributionBytes mode layout).length ≤ maskField mode layout := by
    rw [high]
    omega
  have pendingAfter : distributionStart mode layout+(distributionBytes mode layout).length ≤ pendingField mode layout := by
    rw [high]
    omega
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr maskAfter),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl geometry.1),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr pendingAfter),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr maskAfter)]
  exact distribution_current mode layout candidate ruleOld targetOld fresh state.memory intact

theorem prefix_update_intact (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    InputUpdate.Intact mode (updateLayout mode layout) ruleOld fresh (chosen candidate ruleOld)
      (prefixState mode layout candidate ruleOld state).memory := by
  rw [prefix_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have reset := Listing8InputComposition.update_mask_patch mode (updateLayout mode layout) targetOld fresh false false
    state.memory (update_current mode layout candidate ruleOld targetOld fresh state.memory intact)
  have copied := InputUpdate.patch mode (updateLayout mode layout) targetOld ruleOld fresh false _ reset
  have scalarBefore : scalarField mode layout+4 ≤ (updateLayout mode layout).start := by
    have geometry := field_geometry mode layout
    have ⟨owner,scalar,source,dist,update,mask,pending,ending⟩ := positions mode layout
    simp only [updateLayout]
    rw [scalar,update]
    cases mode <;> simp <;> omega
  have framed := InputUpdate.intact_external mode (updateLayout mode layout) ruleOld fresh false _ copied
    (scalarField mode layout) (-(candidate-ruleOld)) (Or.inl scalarBefore)
  exact Listing8InputComposition.update_mask_patch mode (updateLayout mode layout) ruleOld fresh false
    (chosen candidate ruleOld) _ framed

theorem prefix_pc (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    (prefixState mode layout candidate ruleOld state).pc = Arithmetic.encodeNat mode (distributionStart mode layout) := by
  rw [prefix_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact]

theorem prefix_mask (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get (prefixState mode layout candidate ruleOld state).memory (maskField mode layout) =
      InputUpdate.mask (chosen candidate ruleOld) := by
  rw [prefix_effect mode layout candidate ruleOld targetOld fresh capacity state entry intact,DwordCode.get_put]

end SmcTuring.Appendix.Listing8LiteralInput

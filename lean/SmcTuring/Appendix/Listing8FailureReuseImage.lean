module
public import SmcTuring.Appendix.Listing8FailureValues

public section
namespace SmcTuring.Appendix.Listing8FailureReuseImage
open Native Listing8FailureLayout Listing8FailureBounds Listing8FailureImage
/-- Current static fragments and the preserved store constant. Prior mask and AND values are unrestricted. -/
structure Current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) : Prop where
  resetImage : ByteMemory.bytesAt memory l.start (DwordArithmetic.encode (reset mode l)).length=DwordArithmetic.encode (reset mode l)
  ownerImage : ByteMemory.bytesAt memory (ownerPC l) (StringCodec.initialSize mode)=StringInit.bytes mode (ownerPC l) l.sentinel
  comparisonImage : ByteMemory.bytesAt memory (comparisonPC mode l) (Listing8FailComparison.bytes mode (comparison mode l)).length=Listing8FailComparison.bytes mode (comparison mode l)
  postHeaders : DwordPackets.Intact mode (post mode l) memory
  storeOperand : DwordCode.get memory (storePC mode l+6)=original mode l

theorem from_initial (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) (initial : Initial mode l memory) : Current mode l memory := by
  refine ⟨reset_current mode l memory initial,owner_current mode l memory initial,comparison_current mode l memory initial,
    post_initial mode l memory initial,?_⟩
  let a:=DwordArithmetic.encode (DwordPackets.form mode ⟨notPC mode l,.complement,mask mode l⟩ 0)
  let b:=DwordArithmetic.encode (DwordPackets.form mode ⟨storePC mode l,.store,andPC mode l+6⟩ (original mode l))
  let c:=DwordArithmetic.encode (DwordPackets.form mode ⟨andPC mode l,.bitAnd,mask mode l⟩ force)
  let d:=DwordArithmetic.encode (DwordPackets.form mode ⟨xorPC mode l,.bitXor,callPC mode l+1⟩ force)
  have before : ByteMemory.bytesAt memory (storePC mode l) b.length=b := by
    have packet:=ByteWindow.packet memory (notPC mode l) a b (c++d)
      (by simpa only [a,b,c,d,postBytes,List.append_assoc] using post_current mode l _ initial)
    simpa only [a,DwordArithmetic.encode_length,DwordPackets.form,DwordPackets.raw,DwordArithmetic.located,
      DwordArithmetic.relocate,DwordArithmetic.length,storePC] using packet
  exact DwordOperands.value mode ⟨storePC mode l,.store,andPC mode l+6⟩ (original mode l) memory (by intro impossible;cases impossible) before

theorem reset_owner (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    ByteMemory.bytesAt (resetState mode l state).principal.memory (ownerPC l) (StringCodec.initialSize mode)=StringInit.bytes mode (ownerPC l) l.sentinel := by
  rw [reset_window mode l bounds state entry _ _ (Or.inr (by
    have coords:=positions mode l
    change comparisonPC mode l ≤ mask mode l
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega))]
  exact current.ownerImage

theorem owner_effect (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    ownerFinish mode l state={resetState mode l state with principal := {(resetState mode l state).principal with
      pc := Arithmetic.encodeNat mode (comparisonPC mode l)
      accumulator := StringInit.accumulator mode l.sentinel (resetState mode l state)}} :=
  StringInit.effect mode (ownerPC l) l.sentinel _ (reset_pc mode l bounds state entry) (owner_fits mode l bounds)
    (reset_owner mode l bounds state entry current)

theorem comparison_entry (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    (ownerFinish mode l state).principal.pc=Arithmetic.encodeNat mode (comparison mode l).start := by
  rw [owner_effect mode l bounds state entry current]
  rfl

theorem comparison_image (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    ByteMemory.bytesAt (ownerFinish mode l state).principal.memory (comparison mode l).start
      (Listing8FailComparison.bytes mode (comparison mode l)).length=Listing8FailComparison.bytes mode (comparison mode l) := by
  rw [owner_effect mode l bounds state entry current]
  change ByteMemory.bytesAt (resetState mode l state).principal.memory (comparisonPC mode l) _= _
  rw [reset_window mode l bounds state entry _ _ (Or.inr (by
    have coords:=positions mode l
    rw [Listing8FailComparison.bytes_length]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords ⊢ <;> omega))]
  exact current.comparisonImage

theorem comparison_zero (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    DwordCode.get (ownerFinish mode l state).principal.memory (comparison mode l).mask=0 := by
  rw [owner_effect mode l bounds state entry current]
  change DwordCode.get (DwordArithmetic.execute mode (reset mode l) state.principal).memory (mask mode l)=0
  rw [reset_effect mode l bounds state.principal entry,DwordCode.get_put]

theorem owner_cursor (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    MixedMemory.getWord mode (ownerFinish mode l state).principal.memory l.cursor=MixedMemory.getWord mode state.principal.memory l.cursor := by
  rw [owner_effect mode l bounds state entry current]
  change MixedMemory.getWord mode (DwordArithmetic.execute mode (reset mode l) state.principal).memory l.cursor= _
  rw [reset_effect mode l bounds state.principal entry]
  apply MixedFrames.word_after_dword
  right
  have before:=bounds.cursorBefore
  have coords:=positions mode l
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega

theorem owner_source (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    MixedMemory.getWord mode (ownerFinish mode l state).principal.memory (source mode l)=Arithmetic.encodeNat mode l.sentinel := by
  have fits : source mode l < 2^(8*mode.wordBytes) := by
    have cap:=owner_fits mode l bounds
    change comparisonPC mode l < _ at cap
    have sourceEnd:=source_end mode l
    cases mode <;> simp only [Mode.wordBytes] at sourceEnd <;> omega
  have pointer:=StringInit.initialized_pointer mode (ownerPC l) l.sentinel (resetState mode l state).principal.memory
    (owner_fits mode l bounds) (reset_owner mode l bounds state entry current)
  change Execution.load mode (resetState mode l state).principal.memory (Arithmetic.encodeNat mode (source mode l))=_ at pointer
  rw [MixedMemory.load_nat mode _ _ fits] at pointer
  rw [owner_effect mode l bounds state entry current]
  exact pointer

theorem mismatch (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    Listing8FailComparisonEffects.mismatch mode (comparison mode l) (ownerFinish mode l state).principal.memory=
      !(Listing8FailureValues.failed mode l state.principal.memory) := by
  unfold Listing8FailComparisonEffects.mismatch
  change decide (MixedMemory.getWord mode (ownerFinish mode l state).principal.memory l.cursor ≠
    MixedMemory.getWord mode (ownerFinish mode l state).principal.memory (source mode l))=_
  rw [owner_cursor mode l bounds state entry current,owner_source mode l bounds state entry current]
  exact decide_not

theorem comparison_memory (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    (comparisonFinish mode l state).principal.memory=
      DwordCode.put state.principal.memory (mask mode l) (BranchAlgebra.mask (!(Listing8FailureValues.failed mode l state.principal.memory))) := by
  rw [comparisonFinish,Listing8FailComparisonEffects.effect mode (comparison mode l) (comparison_bounds mode l bounds)
    (ownerFinish mode l state) (comparison_zero mode l bounds state entry current),mismatch mode l bounds state entry current,
    owner_effect mode l bounds state entry current]
  change DwordCode.put (DwordArithmetic.execute mode (reset mode l) state.principal).memory (mask mode l) _= _
  rw [reset_effect mode l bounds state.principal entry,DwordCode.put_overwrite]

theorem store_operand (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    DwordCode.get (comparisonFinish mode l state).principal.memory (storePC mode l+6)=original mode l := by
  rw [comparison_memory mode l bounds state entry current,
    DwordDataflow.read_disjoint _ (mask mode l) (storePC mode l+6) _ (Or.inr (by
      simp only [mask,xorPC,andPC,storePC];omega))]
  exact current.storeOperand

theorem post_headers (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    DwordPackets.Intact mode (post mode l) (comparisonFinish mode l state).principal.memory := by
  intro reader member
  have outside:=mask_outside_post_headers mode l reader member
  rw [comparisonFinish,Listing8FailComparisonEffects.effect mode (comparison mode l) (comparison_bounds mode l bounds)
    (ownerFinish mode l state) (comparison_zero mode l bounds state entry current)]
  change ByteMemory.bytesAt (DwordCode.put (ownerFinish mode l state).principal.memory (mask mode l) _) reader.pc 6 = _
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ outside,owner_effect mode l bounds state entry current,
    reset_window mode l bounds state entry reader.pc 6 outside]
  exact current.postHeaders reader member

end SmcTuring.Appendix.Listing8FailureReuseImage

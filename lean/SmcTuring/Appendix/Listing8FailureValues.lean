module
public import SmcTuring.Appendix.Listing8FailureTrace
public import SmcTuring.Native.DwordOperands

public section
namespace SmcTuring.Appendix.Listing8FailureValues
open Native Listing8FailureLayout Listing8FailureBounds Listing8FailureImage Listing8FailureTrace
@[expose] def failed (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) :=
  decide (MixedMemory.getWord mode memory l.cursor=Arithmetic.encodeNat mode l.sentinel)

theorem owner_cursor (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    MixedMemory.getWord mode (ownerFinish mode l state).principal.memory l.cursor=MixedMemory.getWord mode state.principal.memory l.cursor := by
  rw [owner_effect mode l bounds state entry initial]
  change MixedMemory.getWord mode (DwordArithmetic.execute mode (reset mode l) state.principal).memory l.cursor= _
  rw [reset_effect mode l bounds state.principal entry]
  apply MixedFrames.word_after_dword
  right
  have before:=bounds.cursorBefore
  have coords:=positions mode l
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega

theorem owner_source (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    MixedMemory.getWord mode (ownerFinish mode l state).principal.memory (source mode l)=Arithmetic.encodeNat mode l.sentinel := by
  have fits : source mode l < 2^(8*mode.wordBytes) := by
    have cap:=owner_fits mode l bounds
    change comparisonPC mode l < _ at cap
    have sourceEnd:=source_end mode l
    cases mode <;> simp only [Mode.wordBytes] at sourceEnd <;> omega
  have pointer:=StringInit.initialized_pointer mode (ownerPC l) l.sentinel (resetState mode l state).principal.memory
    (owner_fits mode l bounds) (reset_owner mode l bounds state entry initial)
  change Execution.load mode (resetState mode l state).principal.memory (Arithmetic.encodeNat mode (source mode l))=_ at pointer
  rw [MixedMemory.load_nat mode _ _ fits] at pointer
  rw [owner_effect mode l bounds state entry initial]
  exact pointer

theorem mismatch (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    Listing8FailComparisonEffects.mismatch mode (comparison mode l) (ownerFinish mode l state).principal.memory=
      !(failed mode l state.principal.memory) := by
  unfold Listing8FailComparisonEffects.mismatch
  change decide (MixedMemory.getWord mode (ownerFinish mode l state).principal.memory l.cursor ≠
    MixedMemory.getWord mode (ownerFinish mode l state).principal.memory (source mode l))=_
  rw [owner_cursor mode l bounds state entry initial,owner_source mode l bounds state entry initial]
  exact decide_not

theorem comparison_memory (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    (comparisonFinish mode l state).principal.memory=
      DwordCode.put state.principal.memory (mask mode l) (BranchAlgebra.mask (!(failed mode l state.principal.memory))) := by
  rw [comparisonFinish,Listing8FailComparisonEffects.effect mode (comparison mode l) (comparison_bounds mode l bounds)
    (ownerFinish mode l state) (comparison_zero mode l bounds state entry initial),mismatch mode l bounds state entry initial,
    owner_effect mode l bounds state entry initial]
  change DwordCode.put (DwordArithmetic.execute mode (reset mode l) state.principal).memory (mask mode l) _= _
  rw [reset_effect mode l bounds state.principal entry,DwordCode.put_overwrite]

theorem store_operand (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    DwordCode.get (comparisonFinish mode l state).principal.memory (storePC mode l+6)=original mode l := by
  let a:=DwordArithmetic.encode (DwordPackets.form mode ⟨notPC mode l,.complement,mask mode l⟩ 0)
  let b:=DwordArithmetic.encode (DwordPackets.form mode ⟨storePC mode l,.store,andPC mode l+6⟩ (original mode l))
  let c:=DwordArithmetic.encode (DwordPackets.form mode ⟨andPC mode l,.bitAnd,mask mode l⟩ force)
  let d:=DwordArithmetic.encode (DwordPackets.form mode ⟨xorPC mode l,.bitXor,callPC mode l+1⟩ force)
  have before : ByteMemory.bytesAt state.principal.memory (storePC mode l) b.length=b := by
    have packet:=ByteWindow.packet state.principal.memory (notPC mode l) a b (c++d)
      (by simpa only [a,b,c,d,postBytes,List.append_assoc] using post_current mode l _ initial)
    simpa only [a,DwordArithmetic.encode_length,DwordPackets.form,DwordPackets.raw,DwordArithmetic.located,
      DwordArithmetic.relocate,DwordArithmetic.length,storePC] using packet
  apply DwordOperands.value mode ⟨storePC mode l,.store,andPC mode l+6⟩ (original mode l) _ (by intro impossible;cases impossible)
  rw [comparison_memory mode l bounds state entry initial]
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by
    have coords:=positions mode l
    change storePC mode l+10 ≤ mask mode l
    simp only [storePC,mask,xorPC,andPC]
    omega))]
  exact before

theorem mask_complement (exit : Bool) : ~~~(BranchAlgebra.mask (!exit))=InputUpdate.mask exit := by
  cases exit <;> simp [BranchAlgebra.mask,InputUpdate.mask,BitVec.neg_one_eq_allOnes]

theorem memory (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    (finish mode l state).principal.memory=
      DwordCode.put
        (DwordCode.put
          (DwordCode.put state.principal.memory (andPC mode l+6) (original mode l))
          (mask mode l) (original mode l &&& InputUpdate.mask (failed mode l state.principal.memory)))
        (callPC mode l+1)
        (DwordCode.get state.principal.memory (callPC mode l+1) ^^^
          (original mode l &&& InputUpdate.mask (failed mode l state.principal.memory))) := by
  have stored:=store_operand mode l bounds state entry initial
  have sm : storePC mode l+10 ≤ mask mode l := by simp only [storePC,mask,xorPC,andPC];omega
  have am : andPC mode l+10 ≤ mask mode l := by simp only [mask,xorPC];omega
  have mc : mask mode l+4 ≤ callPC mode l+1 := by
    cases mode <;> simp [mask,callPC,endPC,stackSpan] <;> omega
  have ac : andPC mode l+10 ≤ callPC mode l+1 := by omega
  have ms (memory : ByteMemory.Memory) (value : BitVec 32) :
      DwordCode.get (DwordCode.put memory (mask mode l) value) (storePC mode l+6)=DwordCode.get memory (storePC mode l+6) :=
    DwordDataflow.read_disjoint memory _ _ value (Or.inr sm)
  have ma (memory : ByteMemory.Memory) (value : BitVec 32) :
      DwordCode.get (DwordCode.put memory (mask mode l) value) (andPC mode l+6)=DwordCode.get memory (andPC mode l+6) :=
    DwordDataflow.read_disjoint memory _ _ value (Or.inr am)
  have cm (memory : ByteMemory.Memory) (value : BitVec 32) :
      DwordCode.get (DwordCode.put memory (mask mode l) value) (callPC mode l+1)=DwordCode.get memory (callPC mode l+1) :=
    DwordDataflow.read_disjoint memory _ _ value (Or.inl mc)
  have ca (memory : ByteMemory.Memory) (value : BitVec 32) :
      DwordCode.get (DwordCode.put memory (andPC mode l+6) value) (callPC mode l+1)=DwordCode.get memory (callPC mode l+1) :=
    DwordDataflow.read_disjoint memory _ _ value (Or.inl ac)
  have mm (memory : ByteMemory.Memory) (value : BitVec 32) :
      DwordCode.get (DwordCode.put memory (andPC mode l+6) value) (mask mode l)=DwordCode.get memory (mask mode l) :=
    DwordDataflow.read_disjoint memory _ _ value (Or.inl am)
  have commute (memory : ByteMemory.Memory) (small large : BitVec 32) :
      DwordCode.put (DwordCode.put memory (mask mode l) small) (andPC mode l+6) large=
        DwordCode.put (DwordCode.put memory (andPC mode l+6) large) (mask mode l) small := by
    apply DwordCode.put_commute
    intro index;have bound:=index.isLt
    simp only [ByteMemory.Inside]
    omega
  change (DwordPackets.finish mode (post mode l) (comparisonFinish mode l state).principal).memory= _
  rw [DwordDataflow.packets mode (post mode l) (notPC mode l) (post_chain mode l) (post_valid mode l bounds)
    _ (comparison_endpoint mode l bounds state entry initial)]
  dsimp only [post,DwordDataflow.packetMemory,DwordPackets.raw,DwordArithmetic.result]
  simp only [ms,ma,cm,ca,mm,DwordCode.get_put,stored]
  rw [comparison_memory mode l bounds state entry initial]
  simp only [DwordCode.get_put,mask_complement,cm]
  simp only [commute,DwordCode.put_overwrite]
  rw [show xorPC mode l+6=mask mode l from rfl,DwordCode.get_put]
  rw [BitVec.and_comm (InputUpdate.mask (failed mode l state.principal.memory)) (original mode l)]

theorem registers (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    (finish mode l state).principal.stack=state.principal.stack ∧
    (finish mode l state).sourceIndex=state.sourceIndex ∧
    (finish mode l state).destinationIndex=state.destinationIndex ∧
    (finish mode l state).backwards=state.backwards ∧
    (finish mode l state).principal.carry=false ∧
    (finish mode l state).principal.accumulator=StringInit.accumulator mode l.sentinel (resetState mode l state) := by
  have last:=DwordPackets.registers mode (post mode l) (comparisonFinish mode l state).principal
  have body:=Listing8FailComparisonEffects.effect mode (comparison mode l) (comparison_bounds mode l bounds)
    (ownerFinish mode l state) (comparison_zero mode l bounds state entry initial)
  have owner:=owner_effect mode l bounds state entry initial
  have stack : (finish mode l state).principal.stack=state.principal.stack := by
    rw [show (finish mode l state).principal.stack=(comparisonFinish mode l state).principal.stack from last.2]
    change (Listing8FailComparison.finish mode (comparison mode l) (ownerFinish mode l state)).principal.stack=_
    rw [body,owner]
    rfl
  have indices : (finish mode l state).sourceIndex=state.sourceIndex ∧
      (finish mode l state).destinationIndex=state.destinationIndex ∧ (finish mode l state).backwards=state.backwards := by
    change (comparisonFinish mode l state).sourceIndex=state.sourceIndex ∧
      (comparisonFinish mode l state).destinationIndex=state.destinationIndex ∧ (comparisonFinish mode l state).backwards=state.backwards
    unfold comparisonFinish
    rw [body,owner]
    exact ⟨rfl,rfl,rfl⟩
  refine ⟨stack,indices.1,indices.2.1,indices.2.2,?_,?_⟩
  · rfl
  · rw [show (finish mode l state).principal.accumulator=(comparisonFinish mode l state).principal.accumulator from last.1]
    unfold comparisonFinish
    rw [body,owner]

theorem window (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory)
    (observed count : Nat)
    (andOutside : andPC mode l+10 ≤ observed ∨ observed+count ≤ andPC mode l+6)
    (maskOutside : mask mode l+4 ≤ observed ∨ observed+count ≤ mask mode l)
    (callOutside : callPC mode l+5 ≤ observed ∨ observed+count ≤ callPC mode l+1) :
    ByteMemory.bytesAt (finish mode l state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [memory mode l bounds state entry initial,
    DwordMixedImage.bytes_frame _ _ _ _ _ (by simpa only [Nat.add_assoc] using callOutside),
    DwordMixedImage.bytes_frame _ _ _ _ _ maskOutside,
    DwordMixedImage.bytes_frame _ _ _ _ _ (by simpa only [Nat.add_assoc] using andOutside)]

end SmcTuring.Appendix.Listing8FailureValues

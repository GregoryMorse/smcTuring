module
public import SmcTuring.Appendix.Listing8FailureReuseImage

public section
namespace SmcTuring.Appendix.Listing8FailureReuseEffects
open Native Listing8FailureLayout Listing8FailureBounds Listing8FailureImage Listing8FailureReuseImage

theorem comparison_endpoint (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    (comparisonFinish mode l state).principal.pc=Arithmetic.encodeNat mode (notPC mode l) :=
  Listing8FailComparison.endpoint mode (comparison mode l) _ (Listing8FailureReuseImage.comparison_entry mode l bounds state entry current)

theorem trace (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    StringControl.Trace mode state (Listing8FailureTrace.program mode l state) (finish mode l state) := by
  have startFits : l.start < 2^(8*mode.wordBytes) := by
    have cap:=bounds.capacity
    have coords:=positions mode l
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega
  have fetched : StringControl.fetch mode state.principal.memory state.principal.pc.toNat=
      some (.previous (StringDwordArithmetic.canonical mode (reset mode l))) := by
    rw [entry,Arithmetic.encode_nat_toNat mode l.start startFits]
    exact StringControl.previous_fetch mode _ _ _ (StringDwordArithmetic.encoding mode _ _ _ current.resetImage)
  have first : StringControl.Trace mode state [.previous (StringDwordArithmetic.canonical mode (reset mode l))] (resetState mode l state) := by
    refine .step fetched ?_
    rw [StringControl.execute,StringDwordArithmetic.execute]
    exact .nil _
  have owner:=StringInitTrace.trace mode (ownerPC l) l.sentinel (resetState mode l state)
    (reset_pc mode l bounds state entry) (owner_fits mode l bounds) bounds.sentinelFits bounds.sentinelOutside
    (Listing8FailureReuseImage.reset_owner mode l bounds state entry current)
  have second : StringControl.Trace mode (resetState mode l state) (Listing8FailureTrace.ownerProgram mode l) (ownerFinish mode l state) := by
    simpa only [Listing8FailureTrace.ownerProgram,ownerFinish,List.map_map,Function.comp_def] using StringControl.previous_trace mode (StringDword.string_trace mode owner)
  have third:=Listing8FailComparison.trace mode (comparison mode l) (comparison_bounds mode l bounds) (ownerFinish mode l state)
    (Listing8FailureReuseImage.comparison_entry mode l bounds state entry current) (Listing8FailureReuseImage.comparison_image mode l bounds state entry current)
  have last:=StringControl.previous_trace mode (DwordPackets.trace mode (post mode l) (notPC mode l) (post_chain mode l)
    (post_valid mode l bounds) (post_outside_headers mode l) (comparisonFinish mode l state)
    (comparison_endpoint mode l bounds state entry current) (Listing8FailureReuseImage.post_headers mode l bounds state entry current))
  exact StringControl.trace_append mode (StringControl.trace_append mode (StringControl.trace_append mode first second) third) last

theorem endpoint (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    (finish mode l state).principal.pc=Arithmetic.encodeNat mode (endPC mode l) := by
  have pc:=DwordPackets.endpoint mode (post mode l) (notPC mode l) (post_chain mode l) (post_valid mode l bounds)
    (comparisonFinish mode l state).principal (comparison_endpoint mode l bounds state entry current)
  rw [post_span] at pc
  have position : notPC mode l+36=endPC mode l := by simp [endPC,xorPC,andPC,storePC,Nat.add_assoc]
  rw [position] at pc
  exact pc

theorem memory (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    (finish mode l state).principal.memory=
      DwordCode.put
        (DwordCode.put
          (DwordCode.put state.principal.memory (andPC mode l+6) (original mode l))
          (mask mode l) (original mode l &&& InputUpdate.mask (Listing8FailureValues.failed mode l state.principal.memory)))
        (callPC mode l+1)
        (DwordCode.get state.principal.memory (callPC mode l+1) ^^^
          (original mode l &&& InputUpdate.mask (Listing8FailureValues.failed mode l state.principal.memory))) := by
  have stored:=Listing8FailureReuseImage.store_operand mode l bounds state entry current
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
    _ (comparison_endpoint mode l bounds state entry current)]
  dsimp only [post,DwordDataflow.packetMemory,DwordPackets.raw,DwordArithmetic.result]
  simp only [ms,ma,cm,ca,mm,DwordCode.get_put,stored]
  rw [Listing8FailureReuseImage.comparison_memory mode l bounds state entry current]
  simp only [DwordCode.get_put,Listing8FailureValues.mask_complement,cm]
  simp only [commute,DwordCode.put_overwrite]
  rw [show xorPC mode l+6=mask mode l from rfl,DwordCode.get_put]
  rw [BitVec.and_comm (InputUpdate.mask (Listing8FailureValues.failed mode l state.principal.memory)) (original mode l)]

theorem registers (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    (finish mode l state).principal.stack=state.principal.stack ∧
    (finish mode l state).sourceIndex=state.sourceIndex ∧
    (finish mode l state).destinationIndex=state.destinationIndex ∧
    (finish mode l state).backwards=state.backwards ∧
    (finish mode l state).principal.carry=false ∧
    (finish mode l state).principal.accumulator=StringInit.accumulator mode l.sentinel (resetState mode l state) := by
  have last:=DwordPackets.registers mode (post mode l) (comparisonFinish mode l state).principal
  have body:=Listing8FailComparisonEffects.effect mode (comparison mode l) (comparison_bounds mode l bounds)
    (ownerFinish mode l state) (Listing8FailureReuseImage.comparison_zero mode l bounds state entry current)
  have owner:=Listing8FailureReuseImage.owner_effect mode l bounds state entry current
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
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory)
    (observed count : Nat)
    (andOutside : andPC mode l+10 ≤ observed ∨ observed+count ≤ andPC mode l+6)
    (maskOutside : mask mode l+4 ≤ observed ∨ observed+count ≤ mask mode l)
    (callOutside : callPC mode l+5 ≤ observed ∨ observed+count ≤ callPC mode l+1) :
    ByteMemory.bytesAt (finish mode l state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [memory mode l bounds state entry current,
    DwordMixedImage.bytes_frame _ _ _ _ _ (by simpa only [Nat.add_assoc] using callOutside),
    DwordMixedImage.bytes_frame _ _ _ _ _ maskOutside,
    DwordMixedImage.bytes_frame _ _ _ _ _ (by simpa only [Nat.add_assoc] using andOutside)]

theorem prefix_window (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory)
    (observed count : Nat) (before : observed+count≤notPC mode l) :
    ByteMemory.bytesAt (finish mode l state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  apply window mode l bounds state entry current observed count
  all_goals right
  all_goals cases mode <;> simp [mask,callPC,endPC,stackSpan,xorPC,andPC,storePC] <;> omega

theorem current_after (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (current : Current mode l state.principal.memory) :
    Current mode l (finish mode l state).principal.memory := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [prefix_window mode l bounds state entry current _ _ (by
      rw [DwordArithmetic.encode_length]
      cases mode <;> simp [reset,DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,notPC,comparisonPC,ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size] <;> omega)]
    exact current.resetImage
  · rw [prefix_window mode l bounds state entry current _ _ (by
      change comparisonPC mode l≤notPC mode l
      cases mode <;> simp [notPC,WordMemoryArithmetic.size] <;> omega)]
    exact current.ownerImage
  · have ending : comparisonPC mode l+(Listing8FailComparison.bytes mode (comparison mode l)).length=notPC mode l := by
      rw [Listing8FailComparison.bytes_length]
      cases mode <;> simp [notPC,WordMemoryArithmetic.size,wordPrefix]
    rw [prefix_window mode l bounds state entry current (comparisonPC mode l)
      (Listing8FailComparison.bytes mode (comparison mode l)).length (Nat.le_of_eq ending)]
    exact current.comparisonImage
  · intro reader member
    have maskOutside:=mask_outside_post_headers mode l reader member
    have andOutside:=(post_outside_headers mode l) ⟨storePC mode l,.store,andPC mode l+6⟩ (by simp [post]) reader member
    have callOutside:=(post_outside_headers mode l) ⟨xorPC mode l,.bitXor,callPC mode l+1⟩ (by simp [post]) reader member
    rw [DwordPackets.Current,window mode l bounds state entry current reader.pc 6
      (by simpa only [Nat.add_assoc] using andOutside) maskOutside (by simpa only [Nat.add_assoc] using callOutside)]
    exact current.postHeaders reader member
  · have kept:=congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes))
      (window mode l bounds state entry current (storePC mode l+6) 4 (Or.inr (by simp [andPC]))
        (Or.inr (by simp [mask,xorPC,andPC])) (Or.inr (by cases mode <;> simp [callPC,endPC,stackSpan,xorPC,andPC] <;> omega)))
    change DwordCode.get (finish mode l state).principal.memory (storePC mode l+6)=DwordCode.get state.principal.memory (storePC mode l+6) at kept
    exact kept.trans current.storeOperand

end SmcTuring.Appendix.Listing8FailureReuseEffects

module
public import SmcTuring.Appendix.Listing8FailureBounds

public section
namespace SmcTuring.Appendix.Listing8FailureImage
open Native Listing8FailureLayout Listing8FailureBounds
@[expose] def Initial (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) :=
  ByteMemory.bytesAt memory l.start (bytes mode l).length=bytes mode l
@[expose] def resetState (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  {state with principal := DwordArithmetic.execute mode (reset mode l) state.principal}
@[expose] def ownerFinish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringExecution.run mode (StringInit.forms mode (ownerPC l) l.sentinel) (resetState mode l state)
@[expose] def comparisonFinish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  Listing8FailComparison.finish mode (comparison mode l) (ownerFinish mode l state)
@[expose] def finish (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  {comparisonFinish mode l state with principal := DwordPackets.finish mode (post mode l) (comparisonFinish mode l state).principal}

theorem reset_current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) (initial : Initial mode l memory) :
    ByteMemory.bytesAt memory l.start (DwordArithmetic.encode (reset mode l)).length=DwordArithmetic.encode (reset mode l) :=
  ByteWindow.packet memory l.start [] _ _ (by simpa only [Initial,bytes,List.nil_append,List.append_assoc] using initial)

theorem owner_current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) (initial : Initial mode l memory) :
    ByteMemory.bytesAt memory (ownerPC l) (StringCodec.initialSize mode)=StringInit.bytes mode (ownerPC l) l.sentinel := by
  have packet:=ByteWindow.packet memory l.start (DwordArithmetic.encode (reset mode l))
    (StringInit.bytes mode (ownerPC l) l.sentinel) (Listing8FailComparison.bytes mode (comparison mode l)++postBytes mode l)
    (by simpa only [Initial,bytes,List.append_assoc] using initial)
  simpa only [DwordArithmetic.encode_length,reset,DwordArithmetic.located,DwordArithmetic.relocate,
    DwordArithmetic.length,StringInit.bytes,StringCodec.initial_length,ownerPC] using packet

theorem comparison_current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) (initial : Initial mode l memory) :
    ByteMemory.bytesAt memory (comparisonPC mode l) (Listing8FailComparison.bytes mode (comparison mode l)).length=
      Listing8FailComparison.bytes mode (comparison mode l) := by
  have packet:=ByteWindow.packet memory l.start
    (DwordArithmetic.encode (reset mode l)++StringInit.bytes mode (ownerPC l) l.sentinel)
    (Listing8FailComparison.bytes mode (comparison mode l)) (postBytes mode l)
    (by simpa only [Initial,bytes,List.append_assoc] using initial)
  simpa only [List.length_append,DwordArithmetic.encode_length,reset,DwordArithmetic.located,DwordArithmetic.relocate,
    DwordArithmetic.length,StringInit.bytes,StringCodec.initial_length,comparisonPC,ownerPC,Nat.add_assoc] using packet

theorem post_current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) (initial : Initial mode l memory) :
    ByteMemory.bytesAt memory (notPC mode l) (postBytes mode l).length=postBytes mode l := by
  have packet:=ByteWindow.packet memory l.start
    (DwordArithmetic.encode (reset mode l)++StringInit.bytes mode (ownerPC l) l.sentinel++
      Listing8FailComparison.bytes mode (comparison mode l)) (postBytes mode l) []
    (by simpa only [Initial,bytes,List.append_nil] using initial)
  have size : (Listing8FailComparison.bytes mode (comparison mode l)).length=6*WordMemoryArithmetic.size mode+7 := by cases mode <;> rfl
  simpa only [List.length_append,DwordArithmetic.encode_length,reset,DwordArithmetic.located,DwordArithmetic.relocate,
    DwordArithmetic.length,StringInit.bytes,StringCodec.initial_length,size,notPC,comparisonPC,ownerPC,Nat.add_assoc] using packet

theorem post_initial (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) (initial : Initial mode l memory) :
    DwordPackets.Intact mode (post mode l) memory := by
  have whole:=post_current mode l memory initial
  let a:=DwordArithmetic.encode (DwordPackets.form mode ⟨notPC mode l,.complement,mask mode l⟩ 0)
  let b:=DwordArithmetic.encode (DwordPackets.form mode ⟨storePC mode l,.store,andPC mode l+6⟩ (original mode l))
  let c:=DwordArithmetic.encode (DwordPackets.form mode ⟨andPC mode l,.bitAnd,mask mode l⟩ force)
  let d:=DwordArithmetic.encode (DwordPackets.form mode ⟨xorPC mode l,.bitXor,callPC mode l+1⟩ force)
  have joined : ByteMemory.bytesAt memory (notPC mode l) (a++b++c++d).length=a++b++c++d := whole
  intro reader member
  simp only [post,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact DwordPackets.initial_header mode _ 0 memory
      (by simpa only [List.length_nil,Nat.add_zero,List.nil_append,List.append_assoc] using ByteWindow.packet memory (notPC mode l) [] a (b++c++d) (by simpa only [List.nil_append,List.append_assoc] using joined))
  · apply DwordPackets.initial_header mode _ (original mode l) memory
    have packet:=ByteWindow.packet memory (notPC mode l) a b (c++d) (by simpa only [List.append_assoc] using joined)
    exact packet
  · apply DwordPackets.initial_header mode _ force memory
    have packet:=ByteWindow.packet memory (notPC mode l) (a++b) c d joined
    simpa only [a,b,c,d,List.length_append,DwordArithmetic.encode_length,DwordPackets.form,DwordPackets.raw,
      DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,storePC,andPC,Nat.add_assoc] using packet
  · apply DwordPackets.initial_header mode _ force memory
    have packet:=ByteWindow.packet memory (notPC mode l) (a++b++c) d [] (by simpa only [List.append_nil] using joined)
    simpa only [a,b,c,d,List.length_append,DwordArithmetic.encode_length,DwordPackets.form,DwordPackets.raw,
      DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,storePC,andPC,xorPC,Nat.add_assoc] using packet

theorem reset_pc (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) :
    (resetState mode l state).principal.pc=Arithmetic.encodeNat mode (ownerPC l) := by
  rw [resetState,reset_effect mode l bounds state.principal entry]

theorem reset_window (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (observed count : Nat)
    (outside : mask mode l+4 ≤ observed ∨ observed+count ≤ mask mode l) :
    ByteMemory.bytesAt (resetState mode l state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [resetState,reset_effect mode l bounds state.principal entry]
  exact DwordMixedImage.bytes_frame _ _ _ _ _ outside

theorem reset_owner (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    ByteMemory.bytesAt (resetState mode l state).principal.memory (ownerPC l) (StringCodec.initialSize mode)=StringInit.bytes mode (ownerPC l) l.sentinel := by
  rw [reset_window mode l bounds state entry _ _ (Or.inr (by
    have coords:=positions mode l
    change comparisonPC mode l ≤ mask mode l
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords <;> omega))]
  exact owner_current mode l _ initial

theorem owner_effect (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    ownerFinish mode l state={resetState mode l state with principal := {(resetState mode l state).principal with
      pc := Arithmetic.encodeNat mode (comparisonPC mode l)
      accumulator := StringInit.accumulator mode l.sentinel (resetState mode l state)}} :=
  StringInit.effect mode (ownerPC l) l.sentinel _ (reset_pc mode l bounds state entry) (owner_fits mode l bounds)
    (reset_owner mode l bounds state entry initial)

theorem comparison_entry (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    (ownerFinish mode l state).principal.pc=Arithmetic.encodeNat mode (comparison mode l).start := by
  rw [owner_effect mode l bounds state entry initial]
  rfl

theorem comparison_image (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    ByteMemory.bytesAt (ownerFinish mode l state).principal.memory (comparison mode l).start
      (Listing8FailComparison.bytes mode (comparison mode l)).length=Listing8FailComparison.bytes mode (comparison mode l) := by
  rw [owner_effect mode l bounds state entry initial]
  change ByteMemory.bytesAt (resetState mode l state).principal.memory (comparisonPC mode l) _= _
  rw [reset_window mode l bounds state entry _ _ (Or.inr (by
    have coords:=positions mode l
    rw [Listing8FailComparison.bytes_length]
    cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords ⊢ <;> omega))]
  exact comparison_current mode l _ initial

theorem comparison_zero (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) (initial : Initial mode l state.principal.memory) :
    DwordCode.get (ownerFinish mode l state).principal.memory (comparison mode l).mask=0 := by
  rw [owner_effect mode l bounds state entry initial]
  change DwordCode.get (DwordArithmetic.execute mode (reset mode l) state.principal).memory (mask mode l)=0
  rw [reset_effect mode l bounds state.principal entry,DwordCode.get_put]

end SmcTuring.Appendix.Listing8FailureImage

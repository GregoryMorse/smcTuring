module
public import SmcTuring.Appendix.Listing8FailureReuseEffects

public section
namespace SmcTuring.Appendix.Listing8FailureReuseTransport
open Native Listing8FailureLayout Listing8FailureReuseImage

theorem current (mode : Mode) (l : Layout) (before after : ByteMemory.Memory) (known : Current mode l before)
    (windows : ∀ observed count, l.start≤observed → observed+count≤endPC mode l →
      ByteMemory.bytesAt after observed count=ByteMemory.bytesAt before observed count) : Current mode l after := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [windows l.start _ (Nat.le_refl _) (by
      rw [DwordArithmetic.encode_length]
      cases mode <;> simp [reset,DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,
        endPC,xorPC,andPC,storePC,notPC,comparisonPC,ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix] <;> omega)]
    exact known.resetImage
  · rw [windows (ownerPC l) _ (by unfold ownerPC;omega) (by
      change comparisonPC mode l≤endPC mode l
      cases mode <;> simp [endPC,xorPC,andPC,storePC,notPC,WordMemoryArithmetic.size,wordPrefix] <;> omega)]
    exact known.ownerImage
  · rw [windows (comparisonPC mode l) _ (by unfold comparisonPC ownerPC;omega) (by
      rw [Listing8FailComparison.bytes_length]
      cases mode <;> simp [endPC,xorPC,andPC,storePC,notPC,WordMemoryArithmetic.size,wordPrefix] <;> omega)]
    exact known.comparisonImage
  · intro reader member
    have span : l.start≤reader.pc ∧ reader.pc+6≤endPC mode l := by
      simp only [post,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals cases mode <;> simp [endPC,xorPC,andPC,storePC,notPC,comparisonPC,ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix] <;> omega
    rw [DwordPackets.Current,windows reader.pc 6 span.1 span.2]
    exact known.postHeaders reader member
  · have kept:=congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes))
      (windows (storePC mode l+6) 4 (by cases mode <;> simp [storePC,notPC,comparisonPC,ownerPC,StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix] <;> omega)
        (by simp [endPC,xorPC,andPC] <;> omega))
    exact kept.trans known.storeOperand

end SmcTuring.Appendix.Listing8FailureReuseTransport

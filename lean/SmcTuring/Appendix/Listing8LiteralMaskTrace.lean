module
public import SmcTuring.Appendix.Listing8LiteralInput
public import SmcTuring.Native.DwordMixedSequence

public section
namespace SmcTuring.Appendix.Listing8LiteralMaskTrace
open Native Listing8LiteralInput
abbrev Dword := BitVec 32

/-- Capacity and placement of the later code-owned destination fields.
The whole interpreter must supply these static facts. -/
structure Valid (mode : Mode) (layout : Layout) : Prop where
  destinationFits : ∀ helper ∈ distributionLayouts mode layout,
    helper.destination+4 ≤ 2^(8*mode.wordBytes)
  outsideInput : ∀ helper ∈ distributionLayouts mode layout,
    helper.destination+4 ≤ layout.start ∨ endPC mode layout ≤ helper.destination
  ranges : ∀ helper ∈ distributionLayouts mode layout, mode = .x64 →
    Relocation.SignedDelta (DwordLayout.thirdPC mode helper) helper.destination

theorem helper_bounds (mode : Mode) (layout : Layout) (helper : DwordLayout.Layout)
    (member : helper ∈ distributionLayouts mode layout) :
    distributionStart mode layout ≤ helper.start ∧
    DwordLayout.endPC mode helper ≤ updateStart mode layout ∧
    helper.source = maskField mode layout := by
  cases mode <;> simp [distributionLayouts,Listing8MaskCopy.distributionLayouts,
    List.mem_cons,List.mem_singleton] at member
  all_goals rcases member with rfl | rfl | rfl | rfl <;>
    simp [distributionStart,updateStart,gap,DwordLayout.endPC,DwordLayout.thirdPC,
      DwordLayout.secondPC,DwordLayout.storeSize] <;> omega

theorem copies_valid (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (valid : Valid mode layout)
    (helper : DwordLayout.Layout) (member : helper ∈ distributionLayouts mode layout) :
    DwordLayout.Admissible mode helper := by
  have ⟨lower,upper,source⟩ := helper_bounds mode layout helper member
  have ⟨owner,scalar,symbol,dist,update,mask,pending,ending⟩ := positions mode layout
  have outside := valid.outsideInput helper member
  have fieldFits := valid.destinationFits helper member
  have sourceBounds : layout.start ≤ maskField mode layout ∧ maskField mode layout+4 ≤ endPC mode layout := by
    rw [mask,ending]
    cases mode <;> simp <;> omega
  have layoutBounds : layout.start ≤ distributionStart mode layout ∧ updateStart mode layout ≤ endPC mode layout := by
    rw [dist,update,ending]
    cases mode <;> simp <;> omega
  refine ⟨by omega,?_,fieldFits,?_,?_,?_,?_,valid.ranges helper member,?_⟩
  · rw [source]; omega
  · rw [source]
    rcases outside with before | after <;> omega
  · right
    rw [source]
    have geometry := field_geometry mode layout
    omega
  · rcases outside with before | after
    · left; omega
    · right; omega
  · intro long
    subst mode
    simp [distributionLayouts,Listing8MaskCopy.distributionLayouts,List.mem_cons,List.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [distributionStart,maskField,updateStart,ownerPC,copyStart,gap,DwordLayout.span,
        DwordLayout.storeSize,DwordLayout.secondPC,Relocation.SignedDelta,Relocation.delta] <;> omega
  · intro long
    subst mode
    simp [distributionLayouts,Listing8MaskCopy.distributionLayouts,List.mem_cons,List.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp [distributionStart,maskField,updateStart,ownerPC,copyStart,gap,DwordLayout.span,
        DwordLayout.storeSize,DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,
        Relocation.SignedDelta,Relocation.delta] <;> omega

theorem chain (mode : Mode) (layout : Layout) :
    DwordMixedSequence.Contiguous mode (distributionStart mode layout) (distributionLayouts mode layout) := by
  cases mode <;> simp [distributionLayouts,Listing8MaskCopy.distributionLayouts,
    DwordMixedSequence.Contiguous,DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,
    DwordLayout.storeSize,Nat.add_assoc]

theorem code_frames (mode : Mode) (layout : Layout) (valid : Valid mode layout) :
    DwordMixedSequence.OutsideCodes mode (distributionLayouts mode layout) := by
  intro writer writerMember reader readerMember
  have readerBounds := helper_bounds mode layout reader readerMember
  have coords := positions mode layout
  rcases coords with ⟨owner,scalar,symbol,dist,update,mask,pending,ending⟩
  have placement : layout.start ≤ distributionStart mode layout ∧ updateStart mode layout ≤ endPC mode layout := by
    rw [dist,update,ending]
    cases mode <;> simp <;> omega
  rcases valid.outsideInput writer writerMember with before | after
  · left; omega
  · right; omega

theorem initial_helpers (mode : Mode) (layout : Layout) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory (distributionStart mode layout) (distributionBytes mode layout).length =
      distributionBytes mode layout) :
    DwordMixedSequence.Intact mode (distributionLayouts mode layout) memory := by
  apply DwordMixedSequence.intact_of_bytes mode _ _ (chain mode layout)
  exact current

@[expose] def finish (mode : Mode) (layout : Layout) (state : Execution.State mode) :=
  DwordMixedSequence.finish mode (distributionLayouts mode layout) state
@[expose] def program (mode : Mode) (layout : Layout) :=
  DwordMixedSequence.program mode (distributionLayouts mode layout)

/-- Both corrected calls (six instructions in x86, twelve in x64) fetch
from the initial group image, restoring the same AND mask source each time. -/
theorem trace (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (valid : Valid mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode (distributionStart mode layout))
    (current : ByteMemory.bytesAt state.memory (distributionStart mode layout) (distributionBytes mode layout).length =
      distributionBytes mode layout) :
    MixedDword.Trace mode state (program mode layout) (finish mode layout state) :=
  DwordMixedSequence.trace mode _ _ (chain mode layout) (copies_valid mode layout capacity valid)
    (code_frames mode layout valid) state entry (initial_helpers mode layout state.memory current)

theorem endpoint (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (valid : Valid mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode (distributionStart mode layout)) :
    (finish mode layout state).pc = Arithmetic.encodeNat mode (updateStart mode layout) := by
  have result := DwordMixedSequence.endpoint mode _ _ (chain mode layout)
    (copies_valid mode layout capacity valid) state entry
  cases mode <;> simpa [finish,distributionLayouts,Listing8MaskCopy.distributionLayouts,List.length_cons,
    DwordLayout.span,DwordLayout.storeSize,updateStart,gap] using result

/-- The AND operand is unchanged at the end of the complete distribution. -/
theorem memory_effect (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (valid : Valid mode layout)
    (value : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (distributionStart mode layout))
    (mask : DwordCode.get state.memory (maskField mode layout) = value) :
    (finish mode layout state).memory =
      DwordMixedSequence.putFields state.memory (distributionLayouts mode layout) value :=
  DwordMixedSequence.memory_effect mode _ _ _ (chain mode layout)
    (copies_valid mode layout capacity valid)
    (fun helper member => (helper_bounds mode layout helper member).2.2) state entry value mask

@[expose] def Separate (mode : Mode) (layout : Layout) : Prop :=
  ∀ writer ∈ distributionLayouts mode layout, ∀ reader ∈ distributionLayouts mode layout,
    writer.destination = reader.destination ∨ writer.destination+4 ≤ reader.destination ∨
      reader.destination+4 ≤ writer.destination

theorem fields_separate (mode : Mode) (layout : Layout)
    (apart : layout.transitionMask+(if mode = .x86 then 4 else 14) ≤ layout.directionMask ∨
      layout.directionMask+(if mode = .x86 then 4 else 14) ≤ layout.transitionMask) :
    Separate mode layout := by
  intro writer writerMember reader readerMember
  cases mode <;>
    simp [distributionLayouts,Listing8MaskCopy.distributionLayouts,List.mem_cons] at writerMember readerMember
  all_goals rcases writerMember with rfl | rfl | rfl | rfl
  all_goals rcases readerMember with rfl | rfl | rfl | rfl
  all_goals simp only [reduceCtorEq,ite_true,ite_false] at apart
  all_goals simp
  all_goals rcases apart with before | after <;> omega

/-- Complete mask-field separation derives the final value of every copied
DWORD, including both high fields in long mode. -/
theorem destinations (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2^(8*mode.wordBytes)) (valid : Valid mode layout)
    (separate : Separate mode layout) (value : Dword) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (distributionStart mode layout))
    (mask : DwordCode.get state.memory (maskField mode layout) = value)
    (reader : DwordLayout.Layout) (member : reader ∈ distributionLayouts mode layout) :
    DwordCode.get (finish mode layout state).memory reader.destination = value := by
  rw [memory_effect mode layout capacity valid value state entry mask]
  exact DwordMixedSequence.putFields_value _ _ _ reader member
    (fun writer writerMember => separate writer writerMember reader member)

theorem x86_masks (layout : Layout)
    (capacity : endPC .x86 layout < 2^(8*Mode.x86.wordBytes)) (valid : Valid .x86 layout)
    (separate : Separate .x86 layout) (condition : Bool) (state : Execution.State .x86)
    (entry : state.pc = Arithmetic.encodeNat .x86 (distributionStart .x86 layout))
    (mask : DwordCode.get state.memory (maskField .x86 layout) = InputUpdate.mask condition) :
    DwordCode.get (finish .x86 layout state).memory layout.transitionMask = InputUpdate.mask condition ∧
    DwordCode.get (finish .x86 layout state).memory layout.directionMask = InputUpdate.mask condition := by
  constructor
  · exact destinations .x86 layout capacity valid separate _ state entry mask
      { start := distributionStart .x86 layout, source := maskField .x86 layout, destination := layout.transitionMask }
      (by simp [distributionLayouts,Listing8MaskCopy.distributionLayouts])
  · exact destinations .x86 layout capacity valid separate _ state entry mask
      { start := distributionStart .x86 layout+17, source := maskField .x86 layout, destination := layout.directionMask }
      (by simp [distributionLayouts,Listing8MaskCopy.distributionLayouts])

theorem x64_masks (layout : Layout)
    (capacity : endPC .x64 layout < 2^(8*Mode.x64.wordBytes)) (valid : Valid .x64 layout)
    (separate : Separate .x64 layout) (condition : Bool) (state : Execution.State .x64)
    (entry : state.pc = Arithmetic.encodeNat .x64 (distributionStart .x64 layout))
    (mask : DwordCode.get state.memory (maskField .x64 layout) = InputUpdate.mask condition) :
    X64.HalfWords.pack (DwordCode.get (finish .x64 layout state).memory layout.transitionMask)
      (DwordCode.get (finish .x64 layout state).memory (layout.transitionMask+10)) =
      (if condition then BitVec.allOnes 64 else 0) ∧
    X64.HalfWords.pack (DwordCode.get (finish .x64 layout state).memory layout.directionMask)
      (DwordCode.get (finish .x64 layout state).memory (layout.directionMask+10)) =
      (if condition then BitVec.allOnes 64 else 0) := by
  have low := destinations .x64 layout capacity valid separate _ state entry mask
    { start := distributionStart .x64 layout, source := maskField .x64 layout, destination := layout.transitionMask }
    (by simp [distributionLayouts,Listing8MaskCopy.distributionLayouts])
  have high := destinations .x64 layout capacity valid separate _ state entry mask
    { start := distributionStart .x64 layout+18, source := maskField .x64 layout, destination := layout.transitionMask+10 }
    (by simp [distributionLayouts,Listing8MaskCopy.distributionLayouts])
  have directionLow := destinations .x64 layout capacity valid separate _ state entry mask
    { start := distributionStart .x64 layout+36, source := maskField .x64 layout, destination := layout.directionMask }
    (by simp [distributionLayouts,Listing8MaskCopy.distributionLayouts])
  have directionHigh := destinations .x64 layout capacity valid separate _ state entry mask
    { start := distributionStart .x64 layout+54, source := maskField .x64 layout, destination := layout.directionMask+10 }
    (by simp [distributionLayouts,Listing8MaskCopy.distributionLayouts])
  simp only at low high directionLow directionHigh
  rw [low,high,directionLow,directionHigh]
  exact ⟨Listing8MaskCopy.repeated_mask condition,Listing8MaskCopy.repeated_mask condition⟩

end SmcTuring.Appendix.Listing8LiteralMaskTrace

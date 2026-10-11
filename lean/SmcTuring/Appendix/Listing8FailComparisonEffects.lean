module
public import SmcTuring.Appendix.Listing8FailComparison
public import SmcTuring.Native.MixedFrames
public import SmcTuring.Appendix.BranchAlgebra

public section
namespace SmcTuring.Appendix.Listing8FailComparisonEffects
open Native Listing8FailComparison
@[expose] def mismatch (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) :=
  decide (MixedMemory.getWord mode memory l.cursor ≠ MixedMemory.getWord mode memory l.source)

theorem mask_from_carry (cf : Bool) : (0 : BitVec 32)-(if cf then 1 else 0) = BranchAlgebra.mask cf := by
  cases cf <;> simp [BranchAlgebra.mask,BitVec.neg_one_eq_allOnes]

/-- Whole-byte restoration follows the actual seven effects. NEG observes
the full pointer, while SBB stores the resulting Boolean as a DWORD. -/
theorem effect (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (zero : DwordCode.get state.principal.memory l.mask=0) :
    finish mode l state = {state with principal := {state.principal with
      pc := Arithmetic.encodeNat mode (endPC mode l)
      carry := BitVec.uaddOverflow
        (MixedMemory.getWord mode state.principal.memory l.cursor-MixedMemory.getWord mode state.principal.memory l.source)
        (MixedMemory.getWord mode state.principal.memory l.source)
      memory := DwordCode.put state.principal.memory l.mask (BranchAlgebra.mask (mismatch mode l state.principal.memory))}} := by
  have cb:=bounds.cursorBeforeSource
  have sb:=bounds.sourceBefore
  have ma:=bounds.maskAfter
  have startBeforeEnd : l.start ≤ endPC mode l := by unfold endPC;omega
  have cm : l.cursor+mode.wordBytes ≤ l.mask := by omega
  have sm : l.source+mode.wordBytes ≤ l.mask := by omega
  have cs (memory : ByteMemory.Memory) (value : Word mode) :
      MixedMemory.getWord mode (ByteMemory.putWord mode memory l.source value) l.cursor = MixedMemory.getWord mode memory l.cursor :=
    MixedFrames.word_after_word mode memory l.source l.cursor value (Or.inr cb)
  have sc (memory : ByteMemory.Memory) (value : Word mode) :
      MixedMemory.getWord mode (ByteMemory.putWord mode memory l.cursor value) l.source = MixedMemory.getWord mode memory l.source :=
    MixedFrames.word_after_word mode memory l.cursor l.source value (Or.inl cb)
  have mc (memory : ByteMemory.Memory) (value : Word mode) :
      DwordCode.get (ByteMemory.putWord mode memory l.cursor value) l.mask = DwordCode.get memory l.mask :=
    DwordDataflow.word_frame mode memory l.cursor l.mask value (Or.inl cm)
  have ms (memory : ByteMemory.Memory) (value : Word mode) :
      DwordCode.get (ByteMemory.putWord mode memory l.source value) l.mask = DwordCode.get memory l.mask :=
    DwordDataflow.word_frame mode memory l.source l.mask value (Or.inl sm)
  have cw (memory : ByteMemory.Memory) (value : BitVec 32) :
      MixedMemory.getWord mode (DwordCode.put memory l.mask value) l.cursor = MixedMemory.getWord mode memory l.cursor :=
    MixedFrames.word_after_dword mode memory l.mask l.cursor value (Or.inr cm)
  have sw (memory : ByteMemory.Memory) (value : BitVec 32) :
      MixedMemory.getWord mode (DwordCode.put memory l.mask value) l.source = MixedMemory.getWord mode memory l.source :=
    MixedFrames.word_after_dword mode memory l.mask l.source value (Or.inr sm)
  have putC (memory : ByteMemory.Memory) (small : BitVec 32) (large : Word mode) :
      ByteMemory.putWord mode (DwordCode.put memory l.mask small) l.cursor large =
        DwordCode.put (ByteMemory.putWord mode memory l.cursor large) l.mask small :=
    (MixedMemory.stores_commute mode memory l.cursor l.mask large small (Or.inl cm)).symm
  have putS (memory : ByteMemory.Memory) (small : BitVec 32) (large : Word mode) :
      ByteMemory.putWord mode (DwordCode.put memory l.mask small) l.source large =
        DwordCode.put (ByteMemory.putWord mode memory l.source large) l.mask small :=
    (MixedMemory.stores_commute mode memory l.source l.mask large small (Or.inl sm)).symm
  dsimp only [Listing8FailComparison.finish,sites,ControlPackets.finish,List.foldl_cons,List.foldl_nil,
    ControlPackets.effect,site,offset,target,operation,ControlPackets.size,ControlPackets.accumulator,
    ControlPackets.carry,ControlPackets.memory,WordMemoryArithmetic.accumulator,WordMemoryArithmetic.flag,
    WordMemoryArithmetic.result,DwordArithmetic.result,DwordArithmetic.flag]
  simp only [show ((0:Fin 7):Nat)=0 from rfl,show ((1:Fin 7):Nat)=1 from rfl,show ((2:Fin 7):Nat)=2 from rfl,show ((3:Fin 7):Nat)=3 from rfl,show ((4:Fin 7):Nat)=4 from rfl,show ((5:Fin 7):Nat)=5 from rfl,show ((6:Fin 7):Nat)=6 from rfl]
  simp only [cs,sc,mc,ms,cw,sw,MixedMemory.get_put,zero,BitVec.neg_neg,BitVec.sub_add_cancel,
    mask_from_carry,ne_eq,MixedFrames.sub_zero]
  simp only [putC,putS,Writes.put_word_overwrite]
  rw [MixedFrames.restored_pair mode state.principal.memory l.source l.cursor state.principal.accumulator (Or.inl cb)]
  have pc : l.start+(5*WordMemoryArithmetic.size mode+7)+WordMemoryArithmetic.size mode = endPC mode l := by unfold endPC;omega
  simp only [pc,mismatch,ne_eq]

theorem cursor (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (zero : DwordCode.get state.principal.memory l.mask=0) :
    MixedMemory.getWord mode (finish mode l state).principal.memory l.cursor = MixedMemory.getWord mode state.principal.memory l.cursor := by
  rw [effect mode l bounds state zero]
  apply MixedFrames.word_after_dword
  right
  have cb:=bounds.cursorBeforeSource
  have sb:=bounds.sourceBefore
  have ma:=bounds.maskAfter
  have startBeforeEnd : l.start ≤ endPC mode l := by unfold endPC;omega
  omega

theorem mask (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (zero : DwordCode.get state.principal.memory l.mask=0) :
    DwordCode.get (finish mode l state).principal.memory l.mask = BranchAlgebra.mask (mismatch mode l state.principal.memory) := by
  rw [effect mode l bounds state zero,DwordCode.get_put]

theorem accumulator (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (zero : DwordCode.get state.principal.memory l.mask=0) :
    (finish mode l state).principal.accumulator=state.principal.accumulator := by rw [effect mode l bounds state zero]

end SmcTuring.Appendix.Listing8FailComparisonEffects

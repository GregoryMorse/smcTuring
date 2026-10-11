module
public import SmcTuring.Appendix.Listing9PackedLayout

public section
namespace SmcTuring.Appendix.Listing9Image
open Native Listing9PackedLayout

@[expose] def owners (mode : Mode) (start transitions nodes : Nat) (backing : ByteMemory.Memory) :=
  ByteMemory.putBytes (ByteMemory.putBytes backing (pointerOwner mode start transitions nodes)
    (StringInit.bytes mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save))
    (saveOwner mode start transitions nodes) (StringInit.bytes mode (saveOwner mode start transitions nodes) 0)
@[expose] def epilogueImage (mode : Mode) (start transitions nodes : Nat) (backing : ByteMemory.Memory) :=
  let a:=layout mode start transitions nodes
  ByteMemory.putBytes (ByteMemory.putBytes (ByteMemory.putBytes (owners mode start transitions nodes backing)
    (AccumulatorLayout.thirdPC mode a) (Native.encode mode (AccumulatorLayout.third mode a)))
    (AccumulatorLayout.secondPC mode a) (Native.encode mode (AccumulatorLayout.second mode a)))
    a.epilogue (Native.encode mode (AccumulatorLayout.first mode a))
@[expose] def memory (mode : Mode) (start transitions nodes : Nat) (backing : ByteMemory.Memory) :=
  ByteMemory.putBytes (epilogueImage mode start transitions nodes backing) start
    (Native.encode mode (AccumulatorLayout.saveForm mode (layout mode start transitions nodes)))

theorem prologue (mode : Mode) (start transitions nodes : Nat) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (memory mode start transitions nodes backing) start
      (Native.encode mode (AccumulatorLayout.saveForm mode (layout mode start transitions nodes))).length=
      Native.encode mode (AccumulatorLayout.saveForm mode (layout mode start transitions nodes)) := ByteMemory.bytes_at_put _ _ _

theorem prologue_before_epilogue (mode : Mode) (start transitions nodes : Nat) :
    start+(Native.encode mode (AccumulatorLayout.saveForm mode (layout mode start transitions nodes))).length≤epilogue mode start transitions nodes := by
  rw [Native.instruction_length,(AccumulatorLayout.lengths mode (layout mode start transitions nodes)).1]
  exact (bounds_order mode start transitions nodes).1

theorem epilogue_current (mode : Mode) (start transitions nodes : Nat) (backing : ByteMemory.Memory) :
    Listing8AccumulatorExit.Current mode (layout mode start transitions nodes) (memory mode start transitions nodes backing) := by
  let a:=layout mode start transitions nodes
  have prologueBefore:=prologue_before_epilogue mode start transitions nodes
  change start+(Native.encode mode (AccumulatorLayout.saveForm mode a)).length≤a.epilogue at prologueBefore
  have firstEnd : a.epilogue+(Native.encode mode (AccumulatorLayout.first mode a)).length=AccumulatorLayout.secondPC mode a := by
    rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.1];rfl
  have secondEnd : AccumulatorLayout.secondPC mode a+(Native.encode mode (AccumulatorLayout.second mode a)).length=AccumulatorLayout.thirdPC mode a := by
    rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.1];rfl
  have thirdEnd : AccumulatorLayout.thirdPC mode a+(Native.encode mode (AccumulatorLayout.third mode a)).length=saveOwner mode start transitions nodes := by
    rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.2]
    exact (positions mode start transitions nodes).2.2.1
  dsimp only [a] at *
  constructor
  · rw [memory,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl prologueBefore),epilogueImage]
    exact ByteMemory.bytes_at_put _ _ _
  · rw [memory,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by unfold AccumulatorLayout.secondPC;omega)),epilogueImage,
      Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by rw [firstEnd]))]
    exact ByteMemory.bytes_at_put _ _ _
  · rw [memory,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by unfold AccumulatorLayout.thirdPC AccumulatorLayout.secondPC;omega)),epilogueImage,
      Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by rw [firstEnd];unfold AccumulatorLayout.thirdPC;omega)),
      Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by rw [secondEnd]))]
    exact ByteMemory.bytes_at_put _ _ _

theorem later_window (mode : Mode) (start transitions nodes : Nat) (backing : ByteMemory.Memory) (observed count : Nat)
    (after : saveOwner mode start transitions nodes≤observed) :
    ByteMemory.bytesAt (memory mode start transitions nodes backing) observed count=ByteMemory.bytesAt (owners mode start transitions nodes backing) observed count := by
  let a:=layout mode start transitions nodes
  have coords:=positions mode start transitions nodes
  have prologueBefore:=prologue_before_epilogue mode start transitions nodes
  have endFirst : a.epilogue+(Native.encode mode (AccumulatorLayout.first mode a)).length≤saveOwner mode start transitions nodes := by
    rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.1]
    change a.epilogue+AccumulatorLayout.exchangeSize mode≤_
    dsimp [a,layout,saveOwner];omega
  have endSecond : AccumulatorLayout.secondPC mode a+(Native.encode mode (AccumulatorLayout.second mode a)).length≤saveOwner mode start transitions nodes := by
    rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.1]
    change a.epilogue+AccumulatorLayout.exchangeSize mode+AccumulatorLayout.storeSize mode≤_
    dsimp [a,layout,saveOwner];omega
  have endThird : AccumulatorLayout.thirdPC mode a+(Native.encode mode (AccumulatorLayout.third mode a)).length=saveOwner mode start transitions nodes := by
    rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.2];exact coords.2.2.1
  rw [memory,Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by
    have before:=(bounds_order mode start transitions nodes).2.1;omega)),epilogueImage,
    Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (Nat.le_trans endFirst after)),
    Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (Nat.le_trans endSecond after)),
    Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl (by rw [endThird];exact after))]

theorem save_current (mode : Mode) (start transitions nodes : Nat) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (memory mode start transitions nodes backing) (saveOwner mode start transitions nodes) (StringCodec.initialSize mode)=
      StringInit.bytes mode (saveOwner mode start transitions nodes) 0 := by
  rw [later_window mode start transitions nodes backing _ _ (Nat.le_refl _),owners]
  simpa only [StringInit.bytes,StringCodec.initial_length] using ByteMemory.bytes_at_put
    (ByteMemory.putBytes backing (pointerOwner mode start transitions nodes) (StringInit.bytes mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save))
    (saveOwner mode start transitions nodes) (StringInit.bytes mode (saveOwner mode start transitions nodes) 0)

theorem pointer_current (mode : Mode) (start transitions nodes : Nat) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (memory mode start transitions nodes backing) (pointerOwner mode start transitions nodes) (StringCodec.initialSize mode)=
      StringInit.bytes mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save := by
  have before : saveOwner mode start transitions nodes+(StringInit.bytes mode (saveOwner mode start transitions nodes) 0).length≤pointerOwner mode start transitions nodes := by
    rw [StringInit.bytes,StringCodec.initial_length];exact Nat.le_refl _
  rw [later_window mode start transitions nodes backing _ _ (by dsimp [pointerOwner];omega),owners,
    Listing8CopyImage.byte_frame _ _ _ _ _ (Or.inl before)]
  simpa only [StringInit.bytes,StringCodec.initial_length] using ByteMemory.bytes_at_put backing
    (pointerOwner mode start transitions nodes) (StringInit.bytes mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save)

theorem initial_values (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes) (backing : ByteMemory.Memory) :
    Execution.load mode (memory mode start transitions nodes backing) (Arithmetic.encodeNat mode (layout mode start transitions nodes).save)=0 ∧
    Execution.load mode (memory mode start transitions nodes backing) (Arithmetic.encodeNat mode (layout mode start transitions nodes).pointer)=Arithmetic.encodeNat mode (layout mode start transitions nodes).save := by
  have capacity:=owner_capacity mode start transitions nodes bounds
  exact ⟨StringInit.initialized_pointer mode (saveOwner mode start transitions nodes) 0 _ capacity.1 (save_current mode start transitions nodes backing),
    StringInit.initialized_pointer mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save _ capacity.2 (pointer_current mode start transitions nodes backing)⟩

end SmcTuring.Appendix.Listing9Image

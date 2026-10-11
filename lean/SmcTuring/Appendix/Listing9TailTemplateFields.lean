module
public import SmcTuring.Appendix.Listing9Storage
public import SmcTuring.Native.AccumulatorStoreRegions
public import SmcTuring.Native.FixedStackTemplates

public section
namespace SmcTuring.Appendix.Listing9TailTemplateFields
open Native Listing9PackedLayout

@[expose] def entries (mode : Mode) (start transitions nodes : Nat) : List (FixedStackTemplates.Entry mode) :=
  let a:=layout mode start transitions nodes
  [⟨start,FixedStackTemplates.native mode (AccumulatorLayout.saveForm mode a)⟩,
    ⟨a.epilogue,FixedStackTemplates.native mode (AccumulatorLayout.first mode a)⟩,
    ⟨AccumulatorLayout.secondPC mode a,FixedStackTemplates.native mode (AccumulatorLayout.second mode a)⟩,
    ⟨AccumulatorLayout.thirdPC mode a,FixedStackTemplates.native mode (AccumulatorLayout.third mode a)⟩]
@[expose] def Metadata (mode : Mode) (start transitions nodes address count : Nat) : Prop :=
  (address=(layout mode start transitions nodes).save ∨ address=(layout mode start transitions nodes).pointer) ∧ count=mode.wordBytes
@[expose] def Allowed (mode : Mode) (start transitions nodes address count : Nat) : Prop :=
  (origin mode start≤address ∧ address+count≤epilogue mode start transitions nodes) ∨ Metadata mode start transitions nodes address count

theorem count (mode : Mode) (start transitions nodes : Nat) : (entries mode start transitions nodes).length=4 := rfl

theorem legal (mode : Mode) (start transitions nodes : Nat) :
    ∀ entry∈entries mode start transitions nodes,FixedStackTemplates.Legal mode entry.instruction := by
  simp [entries,FixedStackTemplates.native,FixedStackTemplates.Legal,StringForm.Legal]

theorem entry_bounds (mode : Mode) (start transitions nodes : Nat) (entry : FixedStackTemplates.Entry mode)
    (member : entry∈entries mode start transitions nodes) :
    (entry.pc=start ∧ entry.pc+(FixedStackTemplates.encode mode entry.instruction).length=origin mode start) ∨
    (epilogue mode start transitions nodes≤entry.pc ∧
      entry.pc+(FixedStackTemplates.encode mode entry.instruction).length≤saveOwner mode start transitions nodes) := by
  simp only [entries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals cases mode
  all_goals simp [FixedStackTemplates.encode,FixedStackTemplates.native,StringForm.encode,Native.instruction_length,
    AccumulatorLayout.saveForm,AccumulatorLayout.first,AccumulatorLayout.second,AccumulatorLayout.third,
    AccumulatorLayout.secondPC,AccumulatorLayout.thirdPC,AccumulatorLayout.storeSize,AccumulatorLayout.exchangeSize,
    Reader.storeForm,Native.instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix,Mode.wordBytes,layout,origin,saveOwner]
  all_goals omega

theorem fixed_frames (mode : Mode) (start transitions nodes address size : Nat)
    (allowed : Allowed mode start transitions nodes address size) :
    FixedStackTemplates.OutsideAll mode (entries mode start transitions nodes) address size := by
  have ordered:=bounds_order mode start transitions nodes
  intro entry member
  have windows:=entry_bounds mode start transitions nodes entry member
  rcases allowed with body | metadata
  · rcases windows with early | late
    · exact Or.inr (by rw [early.2];exact body.1)
    · exact Or.inl (Nat.le_trans body.2 late.1)
  · rcases metadata with ⟨a | b,rfl⟩
    all_goals subst address
    all_goals rcases windows with early | late
    all_goals omega

theorem owner_frames (mode : Mode) (start transitions nodes address size : Nat)
    (allowed : Allowed mode start transitions nodes address size) :
    (address+size≤saveOwner mode start transitions nodes ∨ StringInit.field mode (saveOwner mode start transitions nodes)≤address) ∧
    (address+size≤pointerOwner mode start transitions nodes ∨ StringInit.field mode (pointerOwner mode start transitions nodes)≤address) := by
  have ordered:=bounds_order mode start transitions nodes
  have coords:=positions mode start transitions nodes
  rcases allowed with body | metadata
  · exact ⟨Or.inl (by omega),Or.inl (by dsimp [pointerOwner];omega)⟩
  · rcases metadata with ⟨a | b,rfl⟩
    all_goals subst address
    · exact ⟨Or.inr (Nat.le_refl _),Or.inl (Nat.le_of_eq coords.2.2.2.1)⟩
    · exact ⟨Or.inr (by change (layout mode start transitions nodes).save≤(layout mode start transitions nodes).pointer;omega),Or.inr (Nat.le_refl _)⟩

theorem initial_fixed (mode : Mode) (start transitions nodes : Nat) (memory : ByteMemory.Memory)
    (prologue : ByteMemory.bytesAt memory start (Native.encode mode (AccumulatorLayout.saveForm mode (layout mode start transitions nodes))).length=
      Native.encode mode (AccumulatorLayout.saveForm mode (layout mode start transitions nodes)))
    (current : Listing8AccumulatorExit.Current mode (layout mode start transitions nodes) memory) :
    FixedStackTemplates.All mode (entries mode start transitions nodes) memory := by
  intro entry member
  simp only [entries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact prologue
  · exact current.first
  · exact current.second
  · exact current.third

end SmcTuring.Appendix.Listing9TailTemplateFields

module
public import SmcTuring.Appendix.Listing8GraphHaltTerminalWrites
public import SmcTuring.Appendix.Listing8ScalarReadClasses
public import SmcTuring.Native.StringPacketReadClasses

public section
namespace SmcTuring.Appendix.Listing8TerminalReadClasses
open Native Listing8CopyImage

theorem original_owners (mode : Mode) (owners : List (Listing8OriginalOwners.Owner mode)) :
    ∀ form∈(Listing8OriginalOwners.program mode owners).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_flatMap.mp innerMember with ⟨owner,_,ownerMember⟩
  cases owner with
  | pointer pc value =>
    simp only [Listing8OriginalOwners.forms,List.mem_map] at ownerMember
    rcases ownerMember with ⟨original,packetMember,rfl⟩
    cases mode <;> simp only [Listing8CopiedPointer.forms,List.mem_cons,List.not_mem_nil,or_false] at packetMember <;>
      rcases packetMember with rfl | rfl | rfl | rfl <;>
      simp [StringStoreWrites.liftDword,StringReadWindows.Local,StringReadWindows.ControlLocal,StringReadWindows.DwordLocal,
        StringReadWindows.StringLocal,StringReadWindows.NativeLocal,Listing8CopiedPointer.first,Listing8CopiedPointer.second,Reader.storeForm]
  | scalar pc value =>
    simp only [Listing8OriginalOwners.forms,List.mem_cons,List.not_mem_nil,or_false] at ownerMember
    subst middle
    cases mode <;> trivial

theorem nodes (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode)) :
    ∀ form∈(Listing8NodeTrace.program mode start table).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  induction table generalizing start with
  | nil => simp [Listing8NodeTrace.program]
  | cons value table ih =>
    simp only [Listing8NodeTrace.program,List.map_append,List.mem_append]
    intro form member
    rcases member with first | later
    · exact original_owners mode _ form first
    · exact ih _ form later

theorem transitions (mode : Mode) (start : Nat) (table : List (Values mode)) :
    ∀ form∈(Listing8TableTrace.program mode start table).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  induction table generalizing start with
  | nil => simp [Listing8TableTrace.program]
  | cons value table ih =>
    simp only [Listing8TableTrace.program,List.map_append,List.mem_append]
    intro form member
    rcases member with first | later
    · exact original_owners mode _ form first
    · exact ih _ form later

theorem reset (mode : Mode) (l : Listing8ResetLayout.Layout) :
    ∀ form∈(Listing8ResetLayout.program mode l).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  simp only [Listing8ResetLayout.program,List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  intro form member
  rcases member with (((rfl | inputCopy) | owner) | transitionCopy) | marker
  · cases mode <;> trivial
  · exact StringScalarLists.word mode _ form inputCopy
  · have mapped : ((StringInit.forms mode (Listing8ResetLayout.ownerPC mode l) l.ttape).map StringDword.Form.string).map (StringStoreWrites.liftDword mode)=
        (StringInit.forms mode (Listing8ResetLayout.ownerPC mode l) l.ttape).map (StringWrites.liftString mode) := by rw [List.map_map];rfl
    rw [mapped] at owner
    exact StringPacketReadClasses.initializers mode _ _ form owner
  · exact StringScalarLists.word mode _ form transitionCopy
  · exact original_owners mode [_] form (by simpa only [Listing8OriginalOwners.program,List.flatMap_cons,List.flatMap_nil,List.append_nil] using marker)

theorem target (mode : Mode) (origin target : Nat) :
    ∀ form∈Listing4TargetLayout.forms mode origin target,StringReadWindows.Local mode form := by
  cases mode <;> simp [Listing4TargetLayout.forms,Listing4TargetLayout.first,Listing4TargetLayout.adjust,
    Listing4TargetLayout.third,Listing4TargetLayout.fourth,Listing4TargetLayout.fifth,StackMemory.form,
    StackAdjust.subtract,WordMemoryArithmetic.form,WordMemoryArithmetic.opcode,StringOperands.subtract,
    StringStack.native,StringDwordCopy.native,StringReadWindows.Local,StringReadWindows.ControlLocal,
    StringReadWindows.DwordLocal,StringReadWindows.StringLocal,StringReadWindows.NativeLocal]

theorem entry (mode : Mode) (origin : Nat) :
    ∀ form∈Listing4EntryLayout.forms mode origin,StringReadWindows.Local mode form := by
  simp only [Listing4EntryLayout.forms,List.mem_append]
  intro form member
  rcases member with boot | later
  · have localBoot : ∀ form∈Listing4Boot.forms mode origin,StringReadWindows.Local mode form := by
      cases mode <;> simp [Listing4Boot.forms,Listing4StackLayout.forms,Listing4StackLayout.first,
      Listing4StackLayout.second,Listing4StackLayout.third,Listing4StackLayout.fourth,
      Listing4JumpLayout.forms,Listing4JumpLayout.prefixForms,Listing4JumpLayout.exchange,
      Listing4JumpLayout.adjust,Listing4JumpLayout.exchangeSaved,Listing4JumpLayout.call,
      StackMemory.form,StringStack.native,StringDwordCopy.native,StringReadWindows.Local,StringReadWindows.ControlLocal,
      StringReadWindows.DwordLocal,StringReadWindows.StringLocal,StringReadWindows.NativeLocal]
    exact localBoot form boot
  · exact target mode _ _ form later

end SmcTuring.Appendix.Listing8TerminalReadClasses

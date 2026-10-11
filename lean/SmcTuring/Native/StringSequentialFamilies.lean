module
public import SmcTuring.Native.StringScalarLists
public import SmcTuring.Native.StringPCSteps
public import SmcTuring.Native.StringDwordSequence
public import SmcTuring.Native.StringRetarget

public section
namespace SmcTuring.Native.StringSequentialFamilies

theorem mixed (mode : Mode) (forms : List (MixedDword.Form mode)) :
    ∀ form∈((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)),StringPCSteps.Sequential mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_map.mp innerMember with ⟨original,_,rfl⟩
  cases original with
  | arithmetic form => cases mode <;> cases form <;> trivial
  | copy form => cases mode <;> cases form <;> trivial
  | wideExchange => trivial

theorem word (mode : Mode) (layout : ConversionLayout.Layout) :
    ∀ form∈(StringDwordCopy.wordProgram mode layout).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  cases mode <;> simp [StringDwordCopy.wordProgram,ConversionLayout.program,ConversionLayout.first,
    ConversionLayout.second,ConversionLayout.third,Reader.storeForm,StringDwordCopy.native,StringStoreWrites.liftDword,
    StringPCSteps.Sequential,StringPCSteps.ControlSequential,StringPCSteps.DwordSequential,
    StringPCSteps.StringSequential,StringPCSteps.NativeSequential]

theorem dword (mode : Mode) (layout : DwordLayout.Layout) :
    ∀ form∈(StringDwordCopy.dwordProgram mode layout).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_map.mp innerMember with ⟨original,_,rfl⟩
  cases mode <;> cases original <;> trivial

theorem sequence (mode : Mode) (layouts : List DwordLayout.Layout) :
    ∀ form∈(StringDwordSequence.program mode layouts).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_flatMap.mp innerMember with ⟨layout,_,itemMember⟩
  exact dword mode layout _ (List.mem_map.mpr ⟨middle,itemMember,rfl⟩)

theorem retargets (mode : Mode) (sites : List DwordRetargetSequence.Site) :
    ∀ form∈(StringRetarget.program mode sites).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_map.mp innerMember with ⟨site,_,rfl⟩
  cases mode <;> trivial

end SmcTuring.Native.StringSequentialFamilies

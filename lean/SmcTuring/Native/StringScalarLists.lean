module
public import SmcTuring.Native.StringReadClasses
public import SmcTuring.Native.StringDwordSequence
public import SmcTuring.Native.StringRetarget

public section
namespace SmcTuring.Native.StringScalarLists

theorem mixed (mode : Mode) (forms : List (MixedDword.Form mode)) :
    ∀ form∈((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)),StringReadWindows.Local mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_map.mp innerMember with ⟨original,_,rfl⟩
  exact StringReadClasses.mixed mode original

theorem word (mode : Mode) (layout : ConversionLayout.Layout) :
    ∀ form∈(StringDwordCopy.wordProgram mode layout).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  cases mode <;> simp [StringDwordCopy.wordProgram,ConversionLayout.program,ConversionLayout.first,
    ConversionLayout.second,ConversionLayout.third,Reader.storeForm,StringDwordCopy.native,StringStoreWrites.liftDword,
    StringReadWindows.Local,StringReadWindows.ControlLocal,StringReadWindows.DwordLocal,
    StringReadWindows.StringLocal,StringReadWindows.NativeLocal]

theorem dword (mode : Mode) (layout : DwordLayout.Layout) :
    ∀ form∈(StringDwordCopy.dwordProgram mode layout).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_map.mp innerMember with ⟨original,_,rfl⟩
  exact StringReadClasses.copy mode original

theorem sequence (mode : Mode) (layouts : List DwordLayout.Layout) :
    ∀ form∈(StringDwordSequence.program mode layouts).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_flatMap.mp innerMember with ⟨layout,_,itemMember⟩
  exact dword mode layout _ (List.mem_map.mpr ⟨middle,itemMember,rfl⟩)

theorem retargets (mode : Mode) (sites : List DwordRetargetSequence.Site) :
    ∀ form∈(StringRetarget.program mode sites).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_map.mp innerMember with ⟨site,_,rfl⟩
  cases mode <;> trivial

end SmcTuring.Native.StringScalarLists

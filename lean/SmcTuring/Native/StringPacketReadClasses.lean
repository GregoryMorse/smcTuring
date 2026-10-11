module
public import SmcTuring.Native.StringScalarLists
public import SmcTuring.Native.DwordPackets
public import SmcTuring.Native.DwordXorSequence
public import SmcTuring.Native.ControlPackets
public import SmcTuring.Native.StringInit

public section
namespace SmcTuring.Native.StringPacketReadClasses

theorem arithmetic (mode : Mode) (form : DwordArithmetic.Form) :
    StringReadWindows.Local mode (StringStoreWrites.liftDword mode (StringDwordArithmetic.canonical mode form)) := by
  cases mode <;> cases form <;> trivial

theorem initializers (mode : Mode) (start value : Nat) :
    ∀ form∈(StringInit.forms mode start value).map (StringWrites.liftString mode),StringReadWindows.Local mode form := by
  cases mode <;> simp [StringInit.forms,StringWrites.liftString,StringReadWindows.Local,StringReadWindows.ControlLocal,
    StringReadWindows.DwordLocal,StringReadWindows.StringLocal,StringReadWindows.NativeLocal]

theorem packets (mode : Mode) (sites : List DwordPackets.Site) (state : Execution.State mode) :
    ∀ form∈(DwordPackets.program mode sites state).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  induction sites generalizing state with
  | nil => simp [DwordPackets.program]
  | cons site sites ih =>
    simp only [DwordPackets.program,List.map_cons,List.mem_cons]
    intro form member
    rcases member with rfl | later
    · exact arithmetic mode _
    · exact ih _ form later

theorem xors (mode : Mode) (layouts : List DwordXorHelper.Layout) :
    ∀ form∈(DwordXorSequence.program mode layouts).map (StringStoreWrites.liftDword mode),StringReadWindows.Local mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_flatMap.mp innerMember with ⟨layout,_,packetMember⟩
  simp only [DwordXorHelper.program,List.mem_cons,List.not_mem_nil,or_false] at packetMember
  rcases packetMember with rfl | rfl | rfl
  · exact StringReadClasses.copy mode _
  · cases mode <;> trivial
  · exact StringReadClasses.copy mode _

theorem controls (mode : Mode) (sites : List ControlPackets.Site) :
    ∀ form∈(ControlPackets.program mode sites).map StringStack.Form.previous,StringReadWindows.Local mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_map.mp innerMember with ⟨site,_,rfl⟩
  cases site with
  | mk pc target operation =>
    cases operation with
    | word op => cases op <;> trivial
    | negate => exact StringReadClasses.negation mode _
    | dword raw => exact arithmetic mode _

end SmcTuring.Native.StringPacketReadClasses

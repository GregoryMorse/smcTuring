module
public import SmcTuring.Appendix.Listing8GlobalStoreSubregions
public import SmcTuring.Native.StringMacroTemplateWrites
public import SmcTuring.Native.BoundedStoreRegions

public section
namespace SmcTuring.Appendix.Listing8GlobalMacroRegions
open Native StringMacroLayout

structure Placement (mode : Mode) (origin : Nat) (p : Params) : Prop where
  code : Listing4EntryLayout.mainPC mode origin≤p.start ∧ endpoint mode p≤Listing8JumpLayout.jumpPC mode origin
  source : Listing8GlobalControlLayout.Allowed mode origin p.source (max p.size mode.wordBytes)
  destination : Listing8GlobalControlLayout.Allowed mode origin p.destination (max p.size mode.wordBytes)

theorem allowed (mode : Mode) (origin : Nat) (p : Params) (placed : Placement mode origin p) (packet : StringWrites.Packet)
    (inside : StringPacketRegions.Allowed mode p packet) :
    Listing8GlobalControlLayout.Allowed mode origin packet.address packet.bytes.length := by
  have fields:=field_coordinates mode p
  have lower:=placed.code.1
  have upper:=placed.code.2
  rcases inside with sourceField | destinationField | source | destination
  · right;left;constructor <;> unfold StringPacketRegions.Within at sourceField <;> omega
  · right;left;constructor <;> unfold StringPacketRegions.Within at destinationField <;> omega
  · exact Listing8GlobalStoreSubregions.within mode origin _ _ _ _ placed.source source.1 source.2
  · exact Listing8GlobalStoreSubregions.within mode origin _ _ _ _ placed.destination destination.1 destination.2

theorem convert (mode : Mode) (origin : Nat) (p : Params) (placed : Placement mode origin p)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode) (regions : StringPacketRegions.Run mode p forms state) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin) forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih => exact ⟨allowed mode origin p placed _ regions.1,ih _ regions.2⟩

theorem regions (mode : Mode) (origin : Nat) (p : Params) (placed : Placement mode origin p)
    (state : StringExecution.State mode) (ready : Ready mode p state) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin)
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state :=
  convert mode origin p placed _ state (StringMacroTemplateWrites.complete mode p state ready)

end SmcTuring.Appendix.Listing8GlobalMacroRegions

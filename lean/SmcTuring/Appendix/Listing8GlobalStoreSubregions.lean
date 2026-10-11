module
public import SmcTuring.Appendix.Listing8GlobalControlLayout

public section
namespace SmcTuring.Appendix.Listing8GlobalStoreSubregions
open Native Listing8GlobalControlLayout

theorem within (mode : Mode) (origin start span address count : Nat)
    (allowed : Allowed mode origin start span) (lower : start≤address) (upper : address+count≤start+span) :
    Allowed mode origin address count := by
  rcases allowed with slots | body | call | later
  · left
    rcases slots with a | b
    · left;constructor <;> omega
    · right;constructor <;> omega
  · right;left;constructor <;> omega
  · right;right;left;constructor <;> omega
  · right;right;right;omega

end SmcTuring.Appendix.Listing8GlobalStoreSubregions

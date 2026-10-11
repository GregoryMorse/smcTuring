module
public import SmcTuring.Appendix.Listing9StorageWrites

public section
namespace SmcTuring.Appendix.Listing9SurroundWrites
open Native Listing9PackedLayout

theorem fields (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes) :
    StringWrites.WordOwned mode start (endPC mode start transitions nodes) (Arithmetic.encodeNat mode (layout mode start transitions nodes).save) ∧
    StringWrites.WordOwned mode start (endPC mode start transitions nodes) (Arithmetic.encodeNat mode (layout mode start transitions nodes).pointer) := by
  have narrow:=Listing9StorageWrites.fields mode start transitions nodes bounds
  have ordered:=bounds_order mode start transitions nodes
  have initial : start≤origin mode start := by dsimp [origin];omega
  have lower : start≤saveOwner mode start transitions nodes := by omega
  exact ⟨⟨Nat.le_trans lower narrow.1.1,narrow.1.2⟩,⟨Nat.le_trans lower narrow.2.1,narrow.2.2⟩⟩

theorem prologue (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringWrites.OwnedRun mode start (endPC mode start transitions nodes)
      [StringStack.native mode (AccumulatorLayout.saveForm mode (layout mode start transitions nodes))] state := by
  have field:=fields mode start transitions nodes bounds
  have address:=AccumulatorImage.save_address mode (layout mode start transitions nodes) (admissible mode start transitions nodes bounds) state.principal entry
  have nativeRun : Writes.OwnedRun mode (StringWrites.WordOwned mode start (endPC mode start transitions nodes))
      [AccumulatorLayout.saveForm mode (layout mode start transitions nodes)] state.principal := by
    change StringWrites.WordOwned mode start (endPC mode start transitions nodes)
      (Writes.address mode (AccumulatorLayout.saveForm mode (layout mode start transitions nodes)) state.principal) ∧ True
    rw [address];exact ⟨field.1,trivial⟩
  exact StringWrites.native_owned_run mode start (endPC mode start transitions nodes) _ state nativeRun

theorem epilogue (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (epilogue mode start transitions nodes)) :
    StringWrites.OwnedRun mode start (endPC mode start transitions nodes)
      (Listing8AccumulatorExit.program mode (layout mode start transitions nodes)) state := by
  have field:=fields mode start transitions nodes bounds
  have nativeRun:=AccumulatorImage.supported_run mode (layout mode start transitions nodes) (admissible mode start transitions nodes bounds)
    state.principal entry (StringWrites.WordOwned mode start (endPC mode start transitions nodes)) field.1 field.2
  have lifted:=StringWrites.native_owned_run mode start (endPC mode start transitions nodes) _ state nativeRun
  exact lifted

end SmcTuring.Appendix.Listing9SurroundWrites

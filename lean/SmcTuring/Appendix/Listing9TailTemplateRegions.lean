module
public import SmcTuring.Appendix.Listing9TailTemplates
public import SmcTuring.Appendix.Listing9StorageWrites

public section
namespace SmcTuring.Appendix.Listing9TailTemplateRegions
open Native Listing9PackedLayout Listing9TailTemplateFields

/-- Each declaration store uses a complete save or pointer operand field. -/
theorem storage (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start transitions nodes))
    (current : Listing9Storage.Current mode start transitions nodes state.principal.memory) :
    StringStoreRegions.Run mode (Allowed mode start transitions nodes) (Listing9Storage.program mode start transitions nodes) state := by
  have capacities:=owner_capacity mode start transitions nodes bounds
  have coords:=positions mode start transitions nodes
  have ordered:=bounds_order mode start transitions nodes
  have saveFits : (layout mode start transitions nodes).save+mode.wordBytes<2^(8*mode.wordBytes) := by
    rw [coords.2.2.2.1]
    have cap:=bounds.capacity;omega
  have first:=StringStoreTemplateRuns.initializer mode (Allowed mode start transitions nodes)
    (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save state entry capacities.1 saveFits current.save
    (Or.inr ⟨Or.inl rfl,rfl⟩) (Or.inr ⟨Or.inl rfl,rfl⟩)
  have next:=Listing9Storage.pointer_entry mode start transitions nodes bounds state entry current
  have second:=StringStoreTemplateRuns.initializer mode (Allowed mode start transitions nodes)
    (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save
    (Listing9Storage.afterSave mode start transitions nodes state) next.1 capacities.2 saveFits
    (by rw [next.2];exact current.pointer) (Or.inr ⟨Or.inr rfl,rfl⟩) (Or.inr ⟨Or.inl rfl,rfl⟩)
  have shape : Listing9Storage.program mode start transitions nodes=
      (StringInit.forms mode (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save).map (StringWrites.liftString mode)++
      (StringInit.forms mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save).map (StringWrites.liftString mode) := by
    simp only [Listing9Storage.program,Listing9Storage.forms,List.map_append,List.map_map,Function.comp_def]
    rfl
  rw [shape,StringStoreRegions.append,StringWrites.run_lift_string]
  exact ⟨first,second⟩

theorem prologue (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringStoreRegions.Run mode (Allowed mode start transitions nodes)
      [StringWrites.liftNative mode (AccumulatorLayout.saveForm mode (layout mode start transitions nodes))] state :=
  AccumulatorStoreRegions.prologue mode _ _ (admissible mode start transitions nodes bounds) state entry (Or.inr ⟨Or.inl rfl,rfl⟩)

theorem epilogue (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (epilogue mode start transitions nodes)) :
    StringStoreRegions.Run mode (Allowed mode start transitions nodes)
      (Listing8AccumulatorExit.program mode (layout mode start transitions nodes)) state :=
  AccumulatorStoreRegions.epilogue mode _ _ (admissible mode start transitions nodes bounds) state entry
    (Or.inr ⟨Or.inl rfl,rfl⟩) (Or.inr ⟨Or.inr rfl,rfl⟩)

/-- Actual interpreter ownership gives this static body interval policy. The
final binding discharges the ownership premise with the original interpreter. -/
theorem body (mode : Mode) (start transitions nodes : Nat) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (owned : StringWrites.OwnedRun mode (origin mode start) (Listing9PackedLayout.epilogue mode start transitions nodes) forms state) :
    StringStoreRegions.Run mode (Allowed mode start transitions nodes) forms state :=
  BoundedStoreRegions.interval mode _ _ _ forms state (fun _ _ a b => Or.inl ⟨a,b⟩) owned

end SmcTuring.Appendix.Listing9TailTemplateRegions

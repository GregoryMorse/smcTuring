module
public import SmcTuring.Appendix.Listing9TailTemplateRegions
public import SmcTuring.Appendix.Listing8GlobalControlLayout

public section
namespace SmcTuring.Appendix.Listing9GlobalControlRegions
open Native Listing9PackedLayout

/-- Both late metadata fields follow the complete Listing 8 table/reset/body. -/
theorem metadata (mode : Mode) (start transitions nodes : Nat) :
    Listing8GlobalControlLayout.Allowed mode (origin mode start) (layout mode start transitions nodes).save mode.wordBytes ∧
    Listing8GlobalControlLayout.Allowed mode (origin mode start) (layout mode start transitions nodes).pointer mode.wordBytes := by
  have table:=Listing8GraphLayout.transition_lower mode (origin mode start) transitions
  have reset:=Listing8GraphLayout.table_before_input mode (origin mode start) transitions
  have node:=Listing8GraphLayout.node_lower mode (origin mode start) transitions nodes
  have ordered:=bounds_order mode start transitions nodes
  change Listing8FullTableImage.start mode (origin mode start)≤Listing8GraphLayout.reset mode (origin mode start) transitions at table
  change Listing8GraphLayout.input mode (origin mode start) transitions≤epilogue mode start transitions nodes at node
  constructor <;> exact Or.inr (Or.inr (Or.inr (by omega)))

theorem prologue (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode (origin mode start))
      [StringWrites.liftNative mode (AccumulatorLayout.saveForm mode (layout mode start transitions nodes))] state :=
  AccumulatorStoreRegions.prologue mode _ _ (admissible mode start transitions nodes bounds) state entry (metadata mode start transitions nodes).1

theorem epilogue (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (epilogue mode start transitions nodes)) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode (origin mode start))
      (Listing8AccumulatorExit.program mode (layout mode start transitions nodes)) state :=
  AccumulatorStoreRegions.epilogue mode _ _ (admissible mode start transitions nodes bounds) state entry
    (metadata mode start transitions nodes).1 (metadata mode start transitions nodes).2

/-- Actual declaration packets and their second-entry restoration determine
all stores; neither a future image nor future ownership is assumed. -/
theorem storage (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start transitions nodes))
    (current : Listing9Storage.Current mode start transitions nodes state.principal.memory) :
    StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode (origin mode start))
      (Listing9Storage.program mode start transitions nodes) state := by
  have capacities:=owner_capacity mode start transitions nodes bounds
  have coords:=positions mode start transitions nodes
  have fields:=metadata mode start transitions nodes
  have saveFits : (layout mode start transitions nodes).save+mode.wordBytes<2^(8*mode.wordBytes) := by
    rw [coords.2.2.2.1]
    have cap:=bounds.capacity;omega
  have first:=StringStoreTemplateRuns.initializer mode (Listing8GlobalControlLayout.Allowed mode (origin mode start))
    (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save state entry capacities.1 saveFits current.save fields.1 fields.1
  have next:=Listing9Storage.pointer_entry mode start transitions nodes bounds state entry current
  have second:=StringStoreTemplateRuns.initializer mode (Listing8GlobalControlLayout.Allowed mode (origin mode start))
    (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save
    (Listing9Storage.afterSave mode start transitions nodes state) next.1 capacities.2 saveFits
    (by rw [next.2];exact current.pointer) fields.2 fields.1
  have shape : Listing9Storage.program mode start transitions nodes=
      (StringInit.forms mode (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save).map (StringWrites.liftString mode)++
      (StringInit.forms mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save).map (StringWrites.liftString mode) := by
    simp only [Listing9Storage.program,Listing9Storage.forms,List.map_append,List.map_map,Function.comp_def]
    rfl
  rw [shape,StringStoreRegions.append,StringWrites.run_lift_string]
  exact ⟨first,second⟩

end SmcTuring.Appendix.Listing9GlobalControlRegions

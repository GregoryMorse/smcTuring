module
public import SmcTuring.Appendix.Listing9Storage
public import SmcTuring.Appendix.Listing9DeclarationWrites

public section
namespace SmcTuring.Appendix.Listing9StorageWrites
open Native Listing9PackedLayout

theorem fields (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes) :
    StringWrites.WordOwned mode (saveOwner mode start transitions nodes) (endPC mode start transitions nodes)
      (Arithmetic.encodeNat mode (layout mode start transitions nodes).save) ∧
    StringWrites.WordOwned mode (saveOwner mode start transitions nodes) (endPC mode start transitions nodes)
      (Arithmetic.encodeNat mode (layout mode start transitions nodes).pointer) := by
  have coords:=positions mode start transitions nodes
  have ordered:=bounds_order mode start transitions nodes
  have cap:=bounds.capacity
  have saveFits : (layout mode start transitions nodes).save<2^(8*mode.wordBytes) := by omega
  have pointerFits : (layout mode start transitions nodes).pointer<2^(8*mode.wordBytes) := by omega
  constructor
  · unfold StringWrites.WordOwned
    rw [Arithmetic.encode_nat_toNat mode _ saveFits]
    exact ⟨ordered.2.2.1,by rw [coords.2.2.2.1];omega⟩
  · unfold StringWrites.WordOwned
    rw [Arithmetic.encode_nat_toNat mode _ pointerFits]
    exact ⟨by omega,Nat.le_of_eq coords.2.2.2.2⟩

/-- Every reached instruction in both trailing declaration packets has a
nonempty write contained in their actual emitted code interval. The indirect
targets follow from the current packets, including the rewritten self-pointer. -/
theorem owned (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start transitions nodes))
    (current : Listing9Storage.Current mode start transitions nodes state.principal.memory) :
    StringWrites.OwnedRun mode (saveOwner mode start transitions nodes) (endPC mode start transitions nodes)
      (Listing9Storage.program mode start transitions nodes) state := by
  have field:=fields mode start transitions nodes bounds
  have capacities:=owner_capacity mode start transitions nodes bounds
  have first:=Listing9DeclarationWrites.owned mode (saveOwner mode start transitions nodes) (endPC mode start transitions nodes)
    (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save state entry capacities.1 current.save field.1 field.1
  have next:=Listing9Storage.pointer_entry mode start transitions nodes bounds state entry current
  have packet : ByteMemory.bytesAt (Listing9Storage.afterSave mode start transitions nodes state).principal.memory
      (pointerOwner mode start transitions nodes) (StringCodec.initialSize mode)=
      StringInit.bytes mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save := by
    rw [next.2];exact current.pointer
  have second:=Listing9DeclarationWrites.owned mode (saveOwner mode start transitions nodes) (endPC mode start transitions nodes)
    (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save
    (Listing9Storage.afterSave mode start transitions nodes state) next.1 capacities.2 packet field.2 field.1
  have shape : Listing9Storage.program mode start transitions nodes=
      (StringInit.forms mode (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save).map (StringWrites.liftString mode)++
      (StringInit.forms mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save).map (StringWrites.liftString mode) := by
    simp only [Listing9Storage.program,Listing9Storage.forms,List.map_append,List.map_map,Function.comp_def]
    rfl
  rw [shape,StringWrites.owned_run_append,StringWrites.run_lift_string]
  exact ⟨first,second⟩

end SmcTuring.Appendix.Listing9StorageWrites

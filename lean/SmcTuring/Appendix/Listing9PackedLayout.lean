module
public import SmcTuring.Appendix.Listing9EarlyImage

public section
namespace SmcTuring.Appendix.Listing9PackedLayout
open Native

@[expose] def origin (mode : Mode) (start : Nat) := start+AccumulatorLayout.storeSize mode
@[expose] def epilogue (mode : Mode) (start transitions nodes : Nat) :=
  Listing8GraphLayout.endPC mode (origin mode start) transitions nodes
@[expose] def saveOwner (mode : Mode) (start transitions nodes : Nat) :=
  epilogue mode start transitions nodes+AccumulatorLayout.exchangeSize mode+AccumulatorLayout.storeSize mode+AccumulatorLayout.exchangeSize mode
@[expose] def pointerOwner (mode : Mode) (start transitions nodes : Nat) := saveOwner mode start transitions nodes+StringCodec.initialSize mode
@[expose] def layout (mode : Mode) (start transitions nodes : Nat) : AccumulatorLayout.Layout :=
  ⟨start,epilogue mode start transitions nodes,StringInit.field mode (saveOwner mode start transitions nodes),StringInit.field mode (pointerOwner mode start transitions nodes)⟩
@[expose] def endPC (mode : Mode) (start transitions nodes : Nat) := pointerOwner mode start transitions nodes+StringCodec.initialSize mode

structure Bounds (mode : Mode) (start transitions nodes : Nat) : Prop where
  capacity : endPC mode start transitions nodes<2^(8*mode.wordBytes)
  reach : mode=.x64 → endPC mode start transitions nodes≤origin mode start+2^31

theorem positions (mode : Mode) (start transitions nodes : Nat) :
    AccumulatorLayout.savedPC mode (layout mode start transitions nodes)=origin mode start ∧
    (layout mode start transitions nodes).epilogue=Listing8GraphLayout.endPC mode (origin mode start) transitions nodes ∧
    AccumulatorLayout.endPC mode (layout mode start transitions nodes)=saveOwner mode start transitions nodes ∧
    (layout mode start transitions nodes).save+mode.wordBytes=pointerOwner mode start transitions nodes ∧
    (layout mode start transitions nodes).pointer+mode.wordBytes=endPC mode start transitions nodes := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · exact StringCodec.field_end mode (saveOwner mode start transitions nodes)
  · exact StringCodec.field_end mode (pointerOwner mode start transitions nodes)

theorem bounds_order (mode : Mode) (start transitions nodes : Nat) :
    origin mode start≤epilogue mode start transitions nodes ∧
    epilogue mode start transitions nodes≤saveOwner mode start transitions nodes ∧
    saveOwner mode start transitions nodes≤(layout mode start transitions nodes).save ∧
    (layout mode start transitions nodes).save<pointerOwner mode start transitions nodes ∧
    pointerOwner mode start transitions nodes≤(layout mode start transitions nodes).pointer ∧
    (layout mode start transitions nodes).pointer<endPC mode start transitions nodes := by
  have body:=Listing9EarlyImage.input_after_origin mode (origin mode start) transitions
  have input:=Listing8GraphLayout.node_lower mode (origin mode start) transitions nodes
  have positive : 0<mode.wordBytes := by cases mode <;> decide
  have coords:=positions mode start transitions nodes
  refine ⟨Nat.le_trans body input,?_,?_,?_,?_,?_⟩
  · dsimp [saveOwner];omega
  · dsimp [layout,StringInit.field];omega
  · have ending:=coords.2.2.2.1;omega
  · dsimp [layout,StringInit.field];omega
  · have ending:=coords.2.2.2.2;omega

theorem admissible (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes) :
    AccumulatorLayout.Admissible mode (layout mode start transitions nodes) := by
  have coords:=positions mode start transitions nodes
  have ordered:=bounds_order mode start transitions nodes
  have cap:=bounds.capacity
  have signed (next target : Nat) (lower : origin mode start≤next) (before : next≤target)
      (upper : target<endPC mode start transitions nodes) (long : mode=.x64) : Relocation.SignedDelta next target := by
    have reach:=bounds.reach long
    unfold Relocation.SignedDelta Relocation.delta
    constructor <;> omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [coords.1];omega
  · rw [coords.2.2.1];omega
  · rw [coords.2.2.2.1];omega
  · rw [coords.2.2.2.2];omega
  · left
    rw [coords.2.2.2.1];exact ordered.2.2.2.2.1
  · rw [coords.1]
    exact signed _ _ (Nat.le_refl _) (by omega) (by omega)
  · apply signed
    · change origin mode start≤epilogue mode start transitions nodes+AccumulatorLayout.exchangeSize mode;omega
    · change epilogue mode start transitions nodes+AccumulatorLayout.exchangeSize mode≤_
      have ending:=coords.2.2.1
      unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC AccumulatorLayout.secondPC at ending
      change epilogue mode start transitions nodes+AccumulatorLayout.exchangeSize mode+AccumulatorLayout.storeSize mode+AccumulatorLayout.exchangeSize mode=saveOwner mode start transitions nodes at ending
      omega
    · exact ordered.2.2.2.2.2
  · apply signed
    · change origin mode start≤epilogue mode start transitions nodes+AccumulatorLayout.exchangeSize mode+AccumulatorLayout.storeSize mode;omega
    · change epilogue mode start transitions nodes+AccumulatorLayout.exchangeSize mode+AccumulatorLayout.storeSize mode≤_
      dsimp [saveOwner] at ordered;omega
    · exact ordered.2.2.2.2.2
  · rw [coords.2.2.1]
    exact signed _ _ (by omega) ordered.2.2.1 (by omega)

theorem owner_capacity (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes) :
    saveOwner mode start transitions nodes+StringCodec.initialSize mode<2^(8*mode.wordBytes) ∧
    pointerOwner mode start transitions nodes+StringCodec.initialSize mode<2^(8*mode.wordBytes) := by
  have cap:=bounds.capacity
  have positive : 0<StringCodec.initialSize mode := by cases mode <;> decide
  change saveOwner mode start transitions nodes+StringCodec.initialSize mode+StringCodec.initialSize mode<2^(8*mode.wordBytes) at cap
  change saveOwner mode start transitions nodes+StringCodec.initialSize mode<2^(8*mode.wordBytes) ∧
    saveOwner mode start transitions nodes+StringCodec.initialSize mode+StringCodec.initialSize mode<2^(8*mode.wordBytes)
  constructor <;> omega

end SmcTuring.Appendix.Listing9PackedLayout

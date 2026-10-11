module
public import SmcTuring.Native.DwordMixedWrites
public import SmcTuring.Native.DwordTemplateCollection

public section
namespace SmcTuring.Native.MixedFieldOwnership

theorem located (mode : Mode) (pc target : Nat) (form : DwordArithmetic.Form) (state : Execution.State mode)
    (direct : DwordArithmetic.direct form=true) (entry : state.pc=Arithmetic.encodeNat mode pc)
    (range : mode=.x64 → Relocation.SignedDelta (pc+DwordArithmetic.length form) target)
    (fits : target<2^(8*mode.wordBytes)) (owned : Nat → Nat → Prop) (targetOwned : owned target 4) :
    owned (MixedDword.address mode (.arithmetic (DwordArithmetic.located mode form pc target)) state).toNat
      (MixedDword.width mode (.arithmetic (DwordArithmetic.located mode form pc target))) := by
  change owned (DwordArithmetic.address mode (DwordArithmetic.located mode form pc target) state).toNat 4
  rw [DwordArithmetic.located_address mode form pc target state direct entry range,Arithmetic.encode_nat_toNat mode _ fits]
  exact targetOwned

theorem copy_lift (mode : Mode) (owned : Nat → Nat → Prop) (forms : List (DwordCode.Form mode))
    (state : Execution.State mode) (actual : DwordCode.OwnedRun mode (fun address => owned address 4) forms state) :
    MixedDword.OwnedRun mode owned (forms.map MixedDword.Form.copy) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih => exact ⟨actual.1,ih _ actual.2⟩

theorem copy (mode : Mode) (layout : DwordLayout.Layout) (valid : DwordLayout.Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode layout.start)
    (owned : Nat → Nat → Prop) (sourceOwned : owned layout.source 4) (destinationOwned : owned layout.destination 4) :
    MixedDword.OwnedRun mode owned ((DwordLayout.program mode layout).map MixedDword.Form.copy) state :=
  copy_lift mode owned _ state (DwordImage.supported_run mode layout valid state entry (fun address => owned address 4) sourceOwned destinationOwned)

theorem sequence (mode : Mode) (layouts : List DwordLayout.Layout) (start : Nat)
    (chain : DwordMixedSequence.Contiguous mode start layouts)
    (valid : ∀ layout∈layouts,DwordLayout.Admissible mode layout)
    (owned : Nat → Nat → Prop) (fields : ∀ layout∈layouts,owned layout.source 4 ∧ owned layout.destination 4)
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode start) :
    MixedDword.OwnedRun mode owned (DwordMixedSequence.program mode layouts) state := by
  induction layouts generalizing start state with
  | nil => trivial
  | cons layout rest ih =>
    have v := valid layout (List.Mem.head _)
    have f := fields layout (List.Mem.head _)
    have location : state.pc=Arithmetic.encodeNat mode layout.start := by rw [chain.1];exact entry
    have first := copy mode layout v state location owned f.1 f.2
    have next : (DwordEffects.finish mode layout state).pc=Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      rw [DwordEffects.effect mode layout v state location]
    have later := ih _ chain.2 (fun item member => valid item (List.Mem.tail _ member))
      (fun item member => fields item (List.Mem.tail _ member)) _ next
    rw [DwordMixedSequence.program,List.flatMap_cons,MixedWriteRuns.owned_run_append,DwordMixedWrites.copy_run]
    exact ⟨first,later⟩

end SmcTuring.Native.MixedFieldOwnership

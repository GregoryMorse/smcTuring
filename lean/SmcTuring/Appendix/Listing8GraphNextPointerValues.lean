module
public import SmcTuring.Appendix.Listing8GraphNextPointers

public section
namespace SmcTuring.Appendix.Listing8GraphNextPointerValues
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem sources (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let v:=liveValues mode origin g node rule target
    let state:=Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed
    MixedMemory.getWord mode state.principal.memory (Listing8PointerCopies.word mode l).source=v.next ∧
    MixedMemory.getWord mode state.principal.memory (pointerField mode (stateEntry mode (transitionParams mode l).destination))=v.newState ∧
    MixedMemory.getWord mode state.principal.memory (pointerField mode (backEntry mode (nodeParams mode l).destination))=v.back ∧
    MixedMemory.getWord mode state.principal.memory (pointerField mode (forwardEntry mode (nodeParams mode l).destination))=v.forward := by
  have retained:=Listing8GraphNextOwners.retained_image mode origin l t g node rule target ctx selected memory seed
  let next:=nextLayout mode origin l g node rule target
  let v:=liveValues mode origin g node rule target
  have operand (source pc : Nat) (value : Word mode)
      (member : Listing8OwnerSequence.Owner.pointer source pc value∈Listing8GraphNextOwners.ownerList mode origin l g node rule target) :
      MixedMemory.getWord mode (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory (pointerField mode pc)=value :=
    Listing8PointerValues.copied_operand mode source pc value _ (retained (.pointer source pc value) member).2
  exact ⟨operand next.sourceTransition (transitionParams mode next).destination v.next (by simp [Listing8GraphNextOwners.ownerList,Listing8OwnerImage.owners,next,v]),
    operand (stateEntry mode next.sourceTransition) (stateEntry mode (transitionParams mode next).destination) v.newState (by simp [Listing8GraphNextOwners.ownerList,Listing8OwnerImage.owners,next,v]),
    operand (backEntry mode next.sourceNode) (backEntry mode (nodeParams mode next).destination) v.back (by simp [Listing8GraphNextOwners.ownerList,Listing8OwnerImage.owners,next,v]),
    operand (forwardEntry mode next.sourceNode) (forwardEntry mode (nodeParams mode next).destination) v.forward (by simp [Listing8GraphNextOwners.ownerList,Listing8OwnerImage.owners,next,v])⟩

theorem transition_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory
      (StringCodec.sourceField mode (secondStart mode l))=(liveValues mode origin g node rule target).next := by
  let state := Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed
  have entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l) :=
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1
  have value := (sources mode origin l t g node rule target ctx selected memory seed).1
  have effect := Listing8PointerCopies.memory_effect mode l t ctx.copies state entry
  rw [value] at effect
  change MixedMemory.getWord mode (Listing8PointerCopies.finish mode l t state).principal.memory
    (Listing8PointerCopies.word mode l).destination = (liveValues mode origin g node rule target).next
  unfold MixedMemory.getWord
  rw [effect,StringDwordSequence.writes_window]
  · change MixedMemory.getWord mode (ByteMemory.putWord mode state.principal.memory
      (Listing8PointerCopies.word mode l).destination (liveValues mode origin g node rule target).next) (Listing8PointerCopies.word mode l).destination = (liveValues mode origin g node rule target).next
    exact MixedMemory.get_put mode _ _ _
  · intro lay member
    right
    have before := Listing8PointerCopies.cursor_before mode l
    have after := Listing8PointerCopies.destination_after mode l t ctx.copies lay member
    have whole := (Listing8PointerCopies.sizes mode l t).2.1
    omega


theorem x64_source_halves (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context .x64 origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State .x64) :
    let memory := (Listing8GraphNextOwners.finish .x64 origin l t g node rule target memory seed).principal.memory
    let v:=liveValues .x64 origin g node rule target
    let stateField := pointerField .x64 (stateEntry .x64 (transitionParams .x64 l).destination)
    let backField := pointerField .x64 (backEntry .x64 (nodeParams .x64 l).destination)
    let forwardField := pointerField .x64 (forwardEntry .x64 (nodeParams .x64 l).destination)
    DwordCode.get memory stateField = X64.HalfWords.low v.newState ∧
    DwordCode.get memory (stateField+4) = X64.HalfWords.high v.newState ∧
    DwordCode.get memory backField = X64.HalfWords.low v.back ∧
    DwordCode.get memory (backField+4) = X64.HalfWords.high v.back ∧
    DwordCode.get memory forwardField = X64.HalfWords.low v.forward ∧
    DwordCode.get memory (forwardField+4) = X64.HalfWords.high v.forward := by
  dsimp only
  have values := (sources .x64 origin l t g node rule target ctx selected memory seed).2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [PointerHalves.low_get,values.1]
  · rw [PointerHalves.high_get,values.1]
  · rw [PointerHalves.low_get,values.2.1]
  · rw [PointerHalves.high_get,values.2.1]
  · rw [PointerHalves.low_get,values.2.2]
  · rw [PointerHalves.high_get,values.2.2]


theorem memory_effect (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let v:=liveValues mode origin g node rule target
    (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory=
      Listing8PointerValues.putPointer mode (Listing8PointerValues.putPointer mode (Listing8PointerValues.putPointer mode
        (ByteMemory.putWord mode (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory
          (StringCodec.sourceField mode (secondStart mode l)) v.next) t.state v.newState) t.back v.back) t.forward v.forward := by
  let v:=liveValues mode origin g node rule target
  let state := Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed
  have entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l) :=
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1
  have sourceWords := sources mode origin l t g node rule target ctx selected memory seed
  have effect := Listing8PointerCopies.memory_effect mode l t ctx.copies state entry
  rw [sourceWords.1] at effect
  change (Listing8PointerCopies.finish mode l t state).principal.memory = _
  rw [effect]
  cases mode with
  | x86 =>
    have a : DwordCode.get state.principal.memory (pointerField .x86 (stateEntry .x86 (transitionParams .x86 l).destination)) = v.newState := sourceWords.2.1
    have c : DwordCode.get state.principal.memory (pointerField .x86 (backEntry .x86 (nodeParams .x86 l).destination)) = v.back := sourceWords.2.2.1
    have d : DwordCode.get state.principal.memory (pointerField .x86 (forwardEntry .x86 (nodeParams .x86 l).destination)) = v.forward := sourceWords.2.2.2
    simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,Listing8PointerCopies.word,List.cons_append,List.nil_append,
      StringDwordSequence.writes,Listing8PointerValues.putPointer,a,c,d]
    rfl
  | x64 =>
    have h := x64_source_halves origin l t g node rule target ctx selected memory seed
    dsimp only at h
    have a : DwordCode.get state.principal.memory (pointerField .x64 (stateEntry .x64 (transitionParams .x64 l).destination)) = X64.HalfWords.low v.newState := h.1
    have c : DwordCode.get state.principal.memory (pointerField .x64 (stateEntry .x64 (transitionParams .x64 l).destination)+4) = X64.HalfWords.high v.newState := h.2.1
    have d : DwordCode.get state.principal.memory (pointerField .x64 (backEntry .x64 (nodeParams .x64 l).destination)) = X64.HalfWords.low v.back := h.2.2.1
    have e : DwordCode.get state.principal.memory (pointerField .x64 (backEntry .x64 (nodeParams .x64 l).destination)+4) = X64.HalfWords.high v.back := h.2.2.2.1
    have f : DwordCode.get state.principal.memory (pointerField .x64 (forwardEntry .x64 (nodeParams .x64 l).destination)) = X64.HalfWords.low v.forward := h.2.2.2.2.1
    have g : DwordCode.get state.principal.memory (pointerField .x64 (forwardEntry .x64 (nodeParams .x64 l).destination)+4) = X64.HalfWords.high v.forward := h.2.2.2.2.2
    simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,Listing8PointerCopies.word,
      List.cons_append,List.nil_append,StringDwordSequence.writes,Listing8PointerValues.putPointer]
    rw [a,c,d,e,f,g]


end SmcTuring.Appendix.Listing8GraphNextPointerValues

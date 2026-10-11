module
public import SmcTuring.Appendix.Listing8MainPrefix

public section
namespace SmcTuring.Appendix.Listing8LoopPointerValues
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets:=Listing8PointerCopies.Targets

theorem sources (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Listing8MainPrefix.Bounds mode l t v)
    (state : StringExecution.State mode) (atMain : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainPrefix.Current mode l t v state.principal.memory) :
      let state:=Listing8MainLiveOwners.finish mode l v state
    MixedMemory.getWord mode state.principal.memory (Listing8PointerCopies.word mode l).source=v.next ∧
    MixedMemory.getWord mode state.principal.memory (pointerField mode (stateEntry mode (transitionParams mode l).destination))=v.newState ∧
    MixedMemory.getWord mode state.principal.memory (pointerField mode (backEntry mode (nodeParams mode l).destination))=v.back ∧
    MixedMemory.getWord mode state.principal.memory (pointerField mode (forwardEntry mode (nodeParams mode l).destination))=v.forward := by
  have retained:=Listing8MainLiveOwners.retained_image mode l v b.resources b.owners b.tapeReach state atMain forward current.copying
  have operand (source pc : Nat) (value : Word mode)
      (member : Listing8OwnerSequence.Owner.pointer source pc value∈Listing8OwnerImage.owners mode l v) :
      MixedMemory.getWord mode (Listing8MainLiveOwners.finish mode l v state).principal.memory (pointerField mode pc)=value :=
    Listing8PointerValues.copied_operand mode source pc value _ (retained (.pointer source pc value) member).2
  exact ⟨operand l.sourceTransition (transitionParams mode l).destination v.next (by simp [Listing8OwnerImage.owners]),
    operand (stateEntry mode l.sourceTransition) (stateEntry mode (transitionParams mode l).destination) v.newState (by simp [Listing8OwnerImage.owners]),
    operand (backEntry mode l.sourceNode) (backEntry mode (nodeParams mode l).destination) v.back (by simp [Listing8OwnerImage.owners]),
    operand (forwardEntry mode l.sourceNode) (forwardEntry mode (nodeParams mode l).destination) v.forward (by simp [Listing8OwnerImage.owners])⟩

theorem transition_cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Listing8MainPrefix.Bounds mode l t v)
    (state : StringExecution.State mode) (atMain : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainPrefix.Current mode l t v state.principal.memory) :
    MixedMemory.getWord mode (Listing8MainPrefix.finish mode l t v state).principal.memory
      (StringCodec.sourceField mode (secondStart mode l))=(v).next := by
  let ready := Listing8MainLiveOwners.finish mode l v state
  have entry : ready.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l) :=
    (Listing8MainLiveOwners.registers mode l v b.resources b.owners b.tapeReach state atMain forward current.copying).1
  have value := (sources mode l t v b state atMain forward current).1
  have effect := Listing8PointerCopies.memory_effect mode l t b.copies ready entry
  rw [value] at effect
  change MixedMemory.getWord mode (Listing8PointerCopies.finish mode l t ready).principal.memory
    (Listing8PointerCopies.word mode l).destination = (v).next
  unfold MixedMemory.getWord
  rw [effect,StringDwordSequence.writes_window]
  · change MixedMemory.getWord mode (ByteMemory.putWord mode ready.principal.memory
      (Listing8PointerCopies.word mode l).destination (v).next) (Listing8PointerCopies.word mode l).destination = (v).next
    exact MixedMemory.get_put mode _ _ _
  · intro lay member
    right
    have before := Listing8PointerCopies.cursor_before mode l
    have after := Listing8PointerCopies.destination_after mode l t b.copies lay member
    have whole := (Listing8PointerCopies.sizes mode l t).2.1
    omega


theorem x64_source_halves (l : Layout) (t : Targets) (v : Values .x64) (b : Listing8MainPrefix.Bounds .x64 l t v)
    (state : StringExecution.State .x64) (atMain : state.principal.pc=Arithmetic.encodeNat .x64 l.start)
    (forward : state.backwards=false) (current : Listing8MainPrefix.Current .x64 l t v state.principal.memory) :
    let memory := (Listing8MainLiveOwners.finish .x64 l v state).principal.memory
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
  have values := (sources .x64 l t v b state atMain forward current).2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [PointerHalves.low_get,values.1]
  · rw [PointerHalves.high_get,values.1]
  · rw [PointerHalves.low_get,values.2.1]
  · rw [PointerHalves.high_get,values.2.1]
  · rw [PointerHalves.low_get,values.2.2]
  · rw [PointerHalves.high_get,values.2.2]


theorem memory_effect (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (b : Listing8MainPrefix.Bounds mode l t v)
    (state : StringExecution.State mode) (atMain : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainPrefix.Current mode l t v state.principal.memory) :
      (Listing8MainPrefix.finish mode l t v state).principal.memory=
      Listing8PointerValues.putPointer mode (Listing8PointerValues.putPointer mode (Listing8PointerValues.putPointer mode
        (ByteMemory.putWord mode (Listing8MainLiveOwners.finish mode l v state).principal.memory
          (StringCodec.sourceField mode (secondStart mode l)) v.next) t.state v.newState) t.back v.back) t.forward v.forward := by
  let ready := Listing8MainLiveOwners.finish mode l v state
  have entry : ready.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l) :=
    (Listing8MainLiveOwners.registers mode l v b.resources b.owners b.tapeReach state atMain forward current.copying).1
  have sourceWords := sources mode l t v b state atMain forward current
  have effect := Listing8PointerCopies.memory_effect mode l t b.copies ready entry
  rw [sourceWords.1] at effect
  change (Listing8PointerCopies.finish mode l t ready).principal.memory = _
  rw [effect]
  cases mode with
  | x86 =>
    have a : DwordCode.get ready.principal.memory (pointerField .x86 (stateEntry .x86 (transitionParams .x86 l).destination)) = v.newState := sourceWords.2.1
    have c : DwordCode.get ready.principal.memory (pointerField .x86 (backEntry .x86 (nodeParams .x86 l).destination)) = v.back := sourceWords.2.2.1
    have d : DwordCode.get ready.principal.memory (pointerField .x86 (forwardEntry .x86 (nodeParams .x86 l).destination)) = v.forward := sourceWords.2.2.2
    simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,Listing8PointerCopies.word,List.cons_append,List.nil_append,
      StringDwordSequence.writes,Listing8PointerValues.putPointer,a,c,d]
    rfl
  | x64 =>
    have h := x64_source_halves l t v b state atMain forward current
    dsimp only at h
    have a : DwordCode.get ready.principal.memory (pointerField .x64 (stateEntry .x64 (transitionParams .x64 l).destination)) = X64.HalfWords.low v.newState := h.1
    have c : DwordCode.get ready.principal.memory (pointerField .x64 (stateEntry .x64 (transitionParams .x64 l).destination)+4) = X64.HalfWords.high v.newState := h.2.1
    have d : DwordCode.get ready.principal.memory (pointerField .x64 (backEntry .x64 (nodeParams .x64 l).destination)) = X64.HalfWords.low v.back := h.2.2.1
    have e : DwordCode.get ready.principal.memory (pointerField .x64 (backEntry .x64 (nodeParams .x64 l).destination)+4) = X64.HalfWords.high v.back := h.2.2.2.1
    have f : DwordCode.get ready.principal.memory (pointerField .x64 (forwardEntry .x64 (nodeParams .x64 l).destination)) = X64.HalfWords.low v.forward := h.2.2.2.2.1
    have g : DwordCode.get ready.principal.memory (pointerField .x64 (forwardEntry .x64 (nodeParams .x64 l).destination)+4) = X64.HalfWords.high v.forward := h.2.2.2.2.2
    simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,Listing8PointerCopies.word,
      List.cons_append,List.nil_append,StringDwordSequence.writes,Listing8PointerValues.putPointer]
    rw [a,c,d,e,f,g]


end SmcTuring.Appendix.Listing8LoopPointerValues

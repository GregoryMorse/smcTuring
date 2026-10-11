module
public import SmcTuring.Appendix.Listing8PointerImage
public import SmcTuring.Native.PointerHalves

public section
namespace SmcTuring.Appendix.Listing8PointerValues
open Native Listing8CopyImage Listing8Prototypes
abbrev Targets := Listing8PointerCopies.Targets

/-- The payload of the copied DEFADDR is read at the physical copied
operand. The original source address in x86's prefix is retained exactly. -/
theorem copied_operand (mode : Mode) (source pc : Nat) (value : Word mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory pc (pointerBytes mode source value).length = pointerBytes mode source value) :
    MixedMemory.getWord mode memory (pointerField mode pc) = value := by
  have packet := ByteWindow.packet memory pc
    (Native.encode mode (.memory .exchangeAcc (ReaderImage.firstDisp mode source)) ++
      Native.encode mode (Reader.storeForm mode (ReaderImage.label mode source) (ReaderImage.secondDisp mode)) ++
      Native.encode mode .exchangeIndirect ++ wordPrefix mode ++ [0xa3])
    (LittleEndian.wordEncode mode.wordBytes value) []
    (by simpa [pointer_shape,List.append_assoc] using current)
  rw [pointer_prefix_length,LittleEndian.word_encode_length] at packet
  have decoded : ByteMemory.readWord mode memory (pointerField mode pc) = some value := by
    change LittleEndian.wordDecode mode.wordBytes (ByteMemory.bytesAt memory (pointerField mode pc) mode.wordBytes) = some value
    rw [pointerField,packet,LittleEndian.word_decode_encode]
  rw [MixedMemory.read_total] at decoded
  exact Option.some.inj decoded

/-- All four live source words come from the executed copied-owner prefix.
No pointer value or later byte image is assumed at the helper entry. -/
theorem sources (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8PointerImage.ownerFinish mode l t v extra seed).principal.memory
      (Listing8PointerCopies.word mode l).source = v.next ∧
    MixedMemory.getWord mode (Listing8PointerImage.ownerFinish mode l t v extra seed).principal.memory
      (pointerField mode (stateEntry mode (transitionParams mode l).destination)) = v.newState ∧
    MixedMemory.getWord mode (Listing8PointerImage.ownerFinish mode l t v extra seed).principal.memory
      (pointerField mode (backEntry mode (nodeParams mode l).destination)) = v.back ∧
    MixedMemory.getWord mode (Listing8PointerImage.ownerFinish mode l t v extra seed).principal.memory
      (pointerField mode (forwardEntry mode (nodeParams mode l).destination)) = v.forward := by
  have retained := Listing8CopiedOwners.retained_image mode l v r b (Listing8PointerImage.backing mode l t extra) seed
  have operand (source pc : Nat) (value : Word mode)
      (member : Listing8OwnerSequence.Owner.pointer source pc value ∈ Listing8OwnerImage.owners mode l v) :
      MixedMemory.getWord mode (Listing8PointerImage.ownerFinish mode l t v extra seed).principal.memory
        (pointerField mode pc) = value :=
    copied_operand mode source pc value _ (retained (.pointer source pc value) member).2
  exact ⟨operand l.sourceTransition (transitionParams mode l).destination v.next (by simp [Listing8OwnerImage.owners]),
    operand (stateEntry mode l.sourceTransition) (stateEntry mode (transitionParams mode l).destination) v.newState (by simp [Listing8OwnerImage.owners]),
    operand (backEntry mode l.sourceNode) (backEntry mode (nodeParams mode l).destination) v.back (by simp [Listing8OwnerImage.owners]),
    operand (forwardEntry mode l.sourceNode) (forwardEntry mode (nodeParams mode l).destination) v.forward (by simp [Listing8OwnerImage.owners])⟩

theorem transition_cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8PointerImage.finish mode l t v extra seed).principal.memory
      (StringCodec.sourceField mode (secondStart mode l)) = v.next := by
  let state := Listing8PointerImage.ownerFinish mode l t v extra seed
  have entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l) :=
    (Listing8CopiedOwners.result mode l v r b _ seed).1
  have value := (sources mode l t v r b extra seed).1
  have effect := Listing8PointerCopies.memory_effect mode l t copies state entry
  rw [value] at effect
  change MixedMemory.getWord mode (Listing8PointerCopies.finish mode l t state).principal.memory
    (Listing8PointerCopies.word mode l).destination = v.next
  unfold MixedMemory.getWord
  rw [effect,StringDwordSequence.writes_window]
  · change MixedMemory.getWord mode (ByteMemory.putWord mode state.principal.memory
      (Listing8PointerCopies.word mode l).destination v.next) (Listing8PointerCopies.word mode l).destination = v.next
    exact MixedMemory.get_put mode _ _ _
  · intro lay member
    right
    have before := Listing8PointerCopies.cursor_before mode l
    have after := Listing8PointerCopies.destination_after mode l t copies lay member
    have whole := (Listing8PointerCopies.sizes mode l t).2.1
    omega

/-- Real helper stores retain the complete input image when the later
state/neighbor packets follow the input region. -/
theorem input_image (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (afterInput : ∀ pc ∈ [t.state,t.back,t.forward], Listing8LiteralInput.endPC mode l.input ≤ pc)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8InputMask.Intact mode l.input v.rule v.tape force v.fresh force
      (Listing8PointerImage.finish mode l t v extra seed).principal.memory := by
  have current := Listing8OwnerInput.input_image mode l v r b (Listing8PointerImage.backing mode l t extra) seed
  have inputSize := Listing8InputMask.bytes_length mode l.input v.rule v.tape force v.fresh force
  let state := Listing8PointerImage.ownerFinish mode l t v extra seed
  have entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l) :=
    (Listing8CopiedOwners.result mode l v r b _ seed).1
  change ByteMemory.bytesAt (Listing8PointerCopies.finish mode l t state).principal.memory l.input.start
    (Listing8InputMask.bytes mode l.input v.rule v.tape force v.fresh force).length = _
  rw [Listing8PointerCopies.window_frame mode l t copies state entry]
  · exact current
  · left
    have before := Listing8PointerCopies.cursor_before mode l
    have later := r.inputAfter;omega
  · intro lay member
    have a := afterInput t.state (by simp)
    have c := afterInput t.back (by simp)
    have d := afterInput t.forward (by simp)
    right
    cases mode with
    | x86 =>
      simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
      rcases member with rfl | rfl | rfl <;> simp <;> omega
    | x64 =>
      simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

theorem x64_source_halves (l : Layout) (t : Targets) (v : Values .x64) (r : Resources .x64 l)
    (b : Listing8CopiedOwners.Bounds .x64 l v) (extra : ByteMemory.Memory) (seed : StringExecution.State .x64) :
    let memory := (Listing8PointerImage.ownerFinish .x64 l t v extra seed).principal.memory
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
  have values := (sources .x64 l t v r b extra seed).2
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [PointerHalves.low_get,values.1]
  · rw [PointerHalves.high_get,values.1]
  · rw [PointerHalves.low_get,values.2.1]
  · rw [PointerHalves.high_get,values.2.1]
  · rw [PointerHalves.low_get,values.2.2]
  · rw [PointerHalves.high_get,values.2.2]

@[expose] def putPointer (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (value : Word mode) :=
  match mode with
  | .x86 => DwordCode.put memory (pc+6) value
  | .x64 => DwordCode.put (DwordCode.put memory (pc+6) (X64.HalfWords.low value)) (pc+16) (X64.HalfWords.high value)

/-- Exact stores of the four actual pointer values, with ten-byte target
packet spacing and four-byte source spacing in the long-mode expansion. -/
theorem memory_effect (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing8PointerImage.finish mode l t v extra seed).principal.memory =
      putPointer mode (putPointer mode (putPointer mode
        (ByteMemory.putWord mode (Listing8PointerImage.ownerFinish mode l t v extra seed).principal.memory
          (StringCodec.sourceField mode (secondStart mode l)) v.next)
        t.state v.newState) t.back v.back) t.forward v.forward := by
  let state := Listing8PointerImage.ownerFinish mode l t v extra seed
  have entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l) :=
    (Listing8CopiedOwners.result mode l v r b _ seed).1
  have sourceWords := sources mode l t v r b extra seed
  have effect := Listing8PointerCopies.memory_effect mode l t copies state entry
  rw [sourceWords.1] at effect
  change (Listing8PointerCopies.finish mode l t state).principal.memory = _
  rw [effect]
  cases mode with
  | x86 =>
    have a : DwordCode.get state.principal.memory (pointerField .x86 (stateEntry .x86 (transitionParams .x86 l).destination)) = v.newState := sourceWords.2.1
    have c : DwordCode.get state.principal.memory (pointerField .x86 (backEntry .x86 (nodeParams .x86 l).destination)) = v.back := sourceWords.2.2.1
    have d : DwordCode.get state.principal.memory (pointerField .x86 (forwardEntry .x86 (nodeParams .x86 l).destination)) = v.forward := sourceWords.2.2.2
    simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,Listing8PointerCopies.word,List.cons_append,List.nil_append,
      StringDwordSequence.writes,putPointer,a,c,d]
    rfl
  | x64 =>
    have h := x64_source_halves l t v r b extra seed
    dsimp only at h
    have a : DwordCode.get state.principal.memory (pointerField .x64 (stateEntry .x64 (transitionParams .x64 l).destination)) = X64.HalfWords.low v.newState := h.1
    have c : DwordCode.get state.principal.memory (pointerField .x64 (stateEntry .x64 (transitionParams .x64 l).destination)+4) = X64.HalfWords.high v.newState := h.2.1
    have d : DwordCode.get state.principal.memory (pointerField .x64 (backEntry .x64 (nodeParams .x64 l).destination)) = X64.HalfWords.low v.back := h.2.2.1
    have e : DwordCode.get state.principal.memory (pointerField .x64 (backEntry .x64 (nodeParams .x64 l).destination)+4) = X64.HalfWords.high v.back := h.2.2.2.1
    have f : DwordCode.get state.principal.memory (pointerField .x64 (forwardEntry .x64 (nodeParams .x64 l).destination)) = X64.HalfWords.low v.forward := h.2.2.2.2.1
    have g : DwordCode.get state.principal.memory (pointerField .x64 (forwardEntry .x64 (nodeParams .x64 l).destination)+4) = X64.HalfWords.high v.forward := h.2.2.2.2.2
    simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,Listing8PointerCopies.word,
      List.cons_append,List.nil_append,StringDwordSequence.writes,putPointer]
    rw [a,c,d,e,f,g]

theorem input_cursor (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8PointerImage.finish mode l t v extra seed).principal.memory
      (StringCodec.sourceField mode l.start) = Arithmetic.encodeNat mode l.sourceNode := by
  let state := Listing8PointerImage.ownerFinish mode l t v extra seed
  have entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l) :=
    (Listing8CopiedOwners.result mode l v r b _ seed).1
  have firstEnd := StringCodec.field_end mode l.start
  have firstBody : StringCodec.bodyStart mode l.start ≤ secondStart mode l := by
    unfold secondStart StringCodec.endpoint StringCodec.bodyEnd;omega
  have cursorStart : secondStart mode l ≤ (Listing8PointerCopies.word mode l).destination := by
    simp only [Listing8PointerCopies.word,StringCodec.sourceField];omega
  have prior := cursor_end mode l
  have codeAfter := (coordinates mode l).2.2
  have whole := (Listing8PointerCopies.sizes mode l t).2.1
  have window := Listing8PointerCopies.window_frame mode l t copies state entry
    (StringCodec.sourceField mode l.start) mode.wordBytes
    (Or.inr (by unfold StringCodec.bodyStart at firstBody;omega))
    (fun lay member => Or.inr (by
      have after := Listing8PointerCopies.destination_after mode l t copies lay member
      omega))
  have framed := congrArg (fun data => BitVec.ofNat (8*mode.wordBytes) (LittleEndian.pack data)) window
  change MixedMemory.getWord mode (Listing8PointerImage.finish mode l t v extra seed).principal.memory _ =
    MixedMemory.getWord mode state.principal.memory _ at framed
  rw [framed]
  exact Listing8OwnerInput.cursor mode l v r b _ seed

/-- Retaining the original node uses only static separation of the later
target fields from that original blueprint. -/
theorem source_node (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (nodeTargets : ∀ lay ∈ Listing8PointerCopies.layouts mode l t,
      lay.destination+4 ≤ l.sourceNode ∨ l.sourceNode+nodeSpan mode ≤ lay.destination)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8PointerImage.finish mode l t v extra seed).principal.memory l.sourceNode
      (sourceNodeBytes mode l v).length = sourceNodeBytes mode l v := by
  let state := Listing8PointerImage.ownerFinish mode l t v extra seed
  have entry : state.principal.pc = Arithmetic.encodeNat mode (codeEnd mode l) :=
    (Listing8CopiedOwners.result mode l v r b _ seed).1
  have count : (sourceNodeBytes mode l v).length = nodeSpan mode := node_length mode _ _ _ _
  have lower := (Listing8PointerCopies.sizes mode l t).2.1
  have before := Listing8PointerCopies.cursor_before mode l
  have cursorStart : l.start ≤ (Listing8PointerCopies.word mode l).destination := by
    have step := endpoint_lower mode l.start (nodeSpan mode)
    change l.start ≤ secondStart mode l at step
    simp only [Listing8PointerCopies.word,StringCodec.sourceField];omega
  change ByteMemory.bytesAt (Listing8PointerCopies.finish mode l t state).principal.memory _ _ = _
  rw [Listing8PointerCopies.window_frame mode l t copies state entry]
  · exact Listing8OwnerInput.source_node mode l v r b _ seed
  · rw [count]
    rcases r.nodeOutside with early | late
    · right;omega
    · left;have after := r.inputAfter;have finish := code_to_input mode l r;omega
  · intro lay member
    simpa only [count] using nodeTargets lay member

theorem tape_symbol (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (nodeTargets : ∀ lay ∈ Listing8PointerCopies.layouts mode l t,
      lay.destination+4 ≤ l.sourceNode ∨ l.sourceNode+nodeSpan mode ≤ lay.destination)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8PointerImage.finish mode l t v extra seed).principal.memory (l.sourceNode+6) = v.tape :=
  (node_values mode l.sourceNode v.tape v.back v.forward _ (source_node mode l t v r b copies nodeTargets extra seed)).1

theorem registers (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (extra : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing8PointerImage.finish mode l t v extra seed).principal.stack = seed.principal.stack ∧
    (Listing8PointerImage.finish mode l t v extra seed).principal.carry = false ∧
    (Listing8PointerImage.finish mode l t v extra seed).sourceIndex = seed.sourceIndex ∧
    (Listing8PointerImage.finish mode l t v extra seed).destinationIndex = seed.destinationIndex ∧
    (Listing8PointerImage.finish mode l t v extra seed).backwards = false ∧
    (Listing8PointerImage.finish mode l t v extra seed).principal.accumulator =
      DwordCode.lift mode (DwordCode.low mode (Listing8PointerImage.ownerFinish mode l t v extra seed).principal.accumulator) := by
  have prior := Listing8OwnerInput.registers mode l v r b (Listing8PointerImage.backing mode l t extra) seed
  have result := Listing8PointerCopies.registers mode l t copies (Listing8PointerImage.ownerFinish mode l t v extra seed)
    (Listing8CopiedOwners.result mode l v r b _ seed).1
  exact ⟨result.1.trans prior.1,result.2.1.trans prior.2.1,result.2.2.2.1.trans prior.2.2.1,
    result.2.2.2.2.1.trans prior.2.2.2.1,result.2.2.2.2.2.trans prior.2.2.2.2,result.2.2.1⟩

end SmcTuring.Appendix.Listing8PointerValues

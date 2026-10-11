module
public import SmcTuring.Appendix.Listing8Prototypes
public import SmcTuring.Native.TemplateCopy

public section
namespace SmcTuring.Appendix.Listing8PrototypeCopy
open Native Listing8Prototypes
abbrev Dword := BitVec 32

/-- Destination-bound blueprint bytes and the complete literal TRANSFERDATA
macro are initialized in the same memory. The blueprint may mix bare DWORD
owners and full-width M01 DEFADDR owners. -/
@[expose] def initialMemory (mode : Mode) (p : StringMacroLayout.Params)
    (payload : List LittleEndian.Byte) (backing : ByteMemory.Memory) :=
  ByteMemory.putBytes (ByteMemory.putBytes backing p.start (StringMacroLayout.bytes mode p)) p.source payload
@[expose] def initialState (mode : Mode) (p : StringMacroLayout.Params)
    (payload : List LittleEndian.Byte) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  { seed with
    principal := { seed.principal with
      pc := Arithmetic.encodeNat mode p.start
      memory := initialMemory mode p payload backing }
    backwards := false }

theorem initial_payload (mode : Mode) (p : StringMacroLayout.Params)
    (payload : List LittleEndian.Byte) (backing : ByteMemory.Memory) :
    ByteMemory.bytesAt (initialMemory mode p payload backing) p.source payload.length = payload :=
  ByteMemory.bytes_at_put _ _ _

theorem initial_macro (mode : Mode) (p : StringMacroLayout.Params)
    (payload : List LittleEndian.Byte) (backing : ByteMemory.Memory)
    (size : p.size = payload.length) (outside : StringMacroLayout.Outside mode p p.source) :
    ByteMemory.bytesAt (initialMemory mode p payload backing) p.start (StringMacroLayout.bytes mode p).length =
      StringMacroLayout.bytes mode p := by
  unfold initialMemory
  rw [ByteMemory.bytes_at_frame]
  · exact ByteMemory.bytes_at_put _ _ _
  · intro index
    have bound := index.isLt
    have length := StringCodec.whole_length mode p.start p.source p.destination p.size
    change (StringMacroLayout.bytes mode p).length = StringMacroLayout.endpoint mode p-p.start at length
    simp only [←size,ByteMemory.Inside]
    unfold StringMacroLayout.Outside at outside
    rcases outside with before | after <;> omega

theorem ready (mode : Mode) (p : StringMacroLayout.Params)
    (payload : List LittleEndian.Byte) (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (size : p.size = payload.length) (resources : TemplateCopy.Resources mode p) :
    StringMacroLayout.Ready mode p (initialState mode p payload backing seed) :=
  ⟨rfl,rfl,resources.sizeFits,resources.codeFits,resources.sourceFits,resources.destinationFits,
    resources.buffers,resources.sourceOutside,resources.destinationOutside,
    initial_macro mode p payload backing size resources.sourceOutside⟩

/-- Complete actual copying execution and exact destination bytes follow
from initialized blueprint bytes and static resources, without a future-image
or future-trace premise. SI/DI and both macro cursor fields are restored by
the existing literal macro proof. -/
theorem original_copy (mode : Mode) (p : StringMacroLayout.Params)
    (payload : List LittleEndian.Byte) (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (size : p.size = payload.length) (resources : TemplateCopy.Resources mode p) :
    let initial := initialState mode p payload backing seed
    StringExecution.Trace mode initial (StringProgram.forms mode p.start p.source p.destination p.size)
      (StringMacroEffects.finish mode p initial) ∧
    ByteMemory.bytesAt (StringMacroEffects.finish mode p initial).principal.memory p.destination payload.length = payload := by
  let initial := initialState mode p payload backing seed
  have prepared := ready mode p payload backing seed size resources
  refine ⟨StringMacroTrace.trace mode p initial prepared,?_⟩
  rw [StringMacroEffects.finish_effect mode p initial prepared]
  change ByteMemory.bytesAt (ByteMemory.putBytes initial.principal.memory p.destination
    (ByteMemory.bytesAt initial.principal.memory p.source p.size)) p.destination payload.length = payload
  have source : ByteMemory.bytesAt initial.principal.memory p.source p.size = payload := by
    rw [size]
    exact initial_payload mode p payload backing
  rw [source]
  exact ByteMemory.bytes_at_put _ _ _

@[expose] def nodeParams (mode : Mode) (start source destination : Nat) : StringMacroLayout.Params :=
  { start := start, source := source, destination := destination, size := nodeSpan mode }
@[expose] def transitionParams (mode : Mode) (start source destination : Nat) : StringMacroLayout.Params :=
  { start := start, source := source, destination := destination, size := transitionSpan mode }

theorem node_copy (mode : Mode) (start source destination : Nat) (symbol : Dword) (back forward : Word mode)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (resources : TemplateCopy.Resources mode (nodeParams mode start source destination)) :
    let p := nodeParams mode start source destination
    let initial := initialState mode p (nodeBytes mode destination symbol back forward) backing seed
    StringExecution.Trace mode initial (StringProgram.forms mode start source destination p.size)
      (StringMacroEffects.finish mode p initial) ∧
    DwordCode.get (StringMacroEffects.finish mode p initial).principal.memory (destination+6) = symbol ∧
    MixedMemory.getWord mode (StringMacroEffects.finish mode p initial).principal.memory
      (pointerField mode (backEntry mode destination)) = back ∧
    MixedMemory.getWord mode (StringMacroEffects.finish mode p initial).principal.memory
      (pointerField mode (forwardEntry mode destination)) = forward := by
  have copied := original_copy mode (nodeParams mode start source destination)
    (nodeBytes mode destination symbol back forward) backing seed (by rw [node_length]; rfl) resources
  exact ⟨copied.1,node_values mode destination symbol back forward _ copied.2⟩

theorem transition_copy (mode : Mode) (start source destination : Nat) (next state : Word mode)
    (current fresh direction : Dword) (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (resources : TemplateCopy.Resources mode (transitionParams mode start source destination)) :
    let p := transitionParams mode start source destination
    let initial := initialState mode p (transitionBytes mode destination next state current fresh direction) backing seed
    StringExecution.Trace mode initial (StringProgram.forms mode start source destination p.size)
      (StringMacroEffects.finish mode p initial) ∧
    MixedMemory.getWord mode (StringMacroEffects.finish mode p initial).principal.memory (pointerField mode destination) = next ∧
    DwordCode.get (StringMacroEffects.finish mode p initial).principal.memory (currentEntry mode destination+6) = current ∧
    DwordCode.get (StringMacroEffects.finish mode p initial).principal.memory (newEntry mode destination+6) = fresh ∧
    DwordCode.get (StringMacroEffects.finish mode p initial).principal.memory (directionEntry mode destination+6) = direction ∧
    MixedMemory.getWord mode (StringMacroEffects.finish mode p initial).principal.memory
      (pointerField mode (stateEntry mode destination)) = state := by
  have copied := original_copy mode (transitionParams mode start source destination)
    (transitionBytes mode destination next state current fresh direction) backing seed
    (by rw [transition_length]; rfl) resources
  exact ⟨copied.1,transition_values mode destination next state current fresh direction _ copied.2⟩

/-- Copying only OPDBLARGSZ=10 bytes cannot initialize either complete
neighbor pointer of the generalized node used by the printed interpreter. -/
theorem short_node_frame (mode : Mode) (p : StringMacroLayout.Params) (state : StringExecution.State mode)
    (ready : StringMacroLayout.Ready mode p state) (size : p.size = 10) :
    MixedMemory.getWord mode (StringMacroEffects.finish mode p state).principal.memory
      (pointerField mode (backEntry mode p.destination)) =
      MixedMemory.getWord mode state.principal.memory (pointerField mode (backEntry mode p.destination)) ∧
    MixedMemory.getWord mode (StringMacroEffects.finish mode p state).principal.memory
      (pointerField mode (forwardEntry mode p.destination)) =
      MixedMemory.getWord mode state.principal.memory (pointerField mode (forwardEntry mode p.destination)) := by
  rw [StringMacroEffects.finish_effect mode p state ready]
  have frame (observed : Nat) (later : p.destination+10 ≤ observed) :
      MixedMemory.getWord mode
        (ByteMemory.putBytes state.principal.memory p.destination (ByteMemory.bytesAt state.principal.memory p.source p.size)) observed =
        MixedMemory.getWord mode state.principal.memory observed := by
    unfold MixedMemory.getWord
    rw [ByteMemory.bytes_at_frame]
    intro index
    have bound := index.isLt
    simp only [ByteMemory.bytes_at_length,size,ByteMemory.Inside]
    omega
  constructor
  · apply frame
    unfold pointerField backEntry
    omega
  · apply frame
    unfold pointerField forwardEntry backEntry
    omega

theorem short_node_zero_counterexample (mode : Mode) (p : StringMacroLayout.Params) (state : StringExecution.State mode)
    (ready : StringMacroLayout.Ready mode p state) (size : p.size = 10) (oldSymbol : Dword)
    (initial : ByteMemory.bytesAt state.principal.memory p.destination (nodeBytes mode p.destination oldSymbol 0 0).length =
      nodeBytes mode p.destination oldSymbol 0 0)
    (expectedBack : Word mode) (nonzero : expectedBack ≠ 0) :
    MixedMemory.getWord mode (StringMacroEffects.finish mode p state).principal.memory
      (pointerField mode (backEntry mode p.destination)) ≠ expectedBack := by
  rw [(short_node_frame mode p state ready size).1,(node_values mode p.destination oldSymbol 0 0 _ initial).2.1]
  exact Ne.symm nonzero

/-- Relocating the whole transition to the DEFADDR operand label overwrites
that next-pointer field with an instruction header. The new entry label
preserves the intended zero next-pointer in the positive complete-copy proof. -/
theorem operand_destination_counterexample :
    MixedMemory.getWord .x86
      (ByteMemory.putBytes (fun _ => 0) (pointerField .x86 0) (transitionBytes .x86 0 0 0 0 0 0))
      (pointerField .x86 0) ≠ 0 ∧
    MixedMemory.getWord .x64
      (ByteMemory.putBytes (fun _ => 0) (pointerField .x64 0) (transitionBytes .x64 0 0 0 0 0 0))
      (pointerField .x64 0) ≠ 0 := by
  decide

/-- Both complete lengths are precisely entry-to-end distances. Naming
boundaries avoids depending on an assembler's optional MOV encoding. -/
theorem end_labels (mode : Mode) (nodeEntry transitionEntry : Nat) :
    nodeEntry+nodeSpan mode-nodeEntry = nodeSpan mode ∧
    transitionEntry+transitionSpan mode-transitionEntry = transitionSpan mode := by
  omega

/-- The actual Listing 7 source node is emitted for its own source address.
TRANSFERDATA copies those exact old-address bytes; MOVEMODEOFFS subsequently
retargets the scalar owner. This complements the destination-bound result. -/
theorem source_node_copy (mode : Mode) (start source destination : Nat) (symbol : Dword) (back forward : Word mode)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (resources : TemplateCopy.Resources mode (nodeParams mode start source destination)) :
    let p := nodeParams mode start source destination
    let initial := initialState mode p (nodeBytes mode source symbol back forward) backing seed
    StringExecution.Trace mode initial (StringProgram.forms mode start source destination p.size)
      (StringMacroEffects.finish mode p initial) ∧
    ByteMemory.bytesAt (StringMacroEffects.finish mode p initial).principal.memory destination
      (nodeBytes mode source symbol back forward).length = nodeBytes mode source symbol back forward :=
  original_copy mode (nodeParams mode start source destination) (nodeBytes mode source symbol back forward) backing seed
    (by rw [node_length]; rfl) resources

theorem source_transition_copy (mode : Mode) (start source destination : Nat) (next state : Word mode)
    (current fresh direction : Dword) (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (resources : TemplateCopy.Resources mode (transitionParams mode start source destination)) :
    let p := transitionParams mode start source destination
    let initial := initialState mode p (transitionBytes mode source next state current fresh direction) backing seed
    StringExecution.Trace mode initial (StringProgram.forms mode start source destination p.size)
      (StringMacroEffects.finish mode p initial) ∧
    ByteMemory.bytesAt (StringMacroEffects.finish mode p initial).principal.memory destination
      (transitionBytes mode source next state current fresh direction).length =
      transitionBytes mode source next state current fresh direction :=
  original_copy mode (transitionParams mode start source destination)
    (transitionBytes mode source next state current fresh direction) backing seed (by rw [transition_length]; rfl) resources

end SmcTuring.Appendix.Listing8PrototypeCopy

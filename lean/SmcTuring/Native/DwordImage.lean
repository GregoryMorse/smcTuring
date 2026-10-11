module
public import SmcTuring.Native.DwordEffects

public section
namespace SmcTuring.Native.DwordImage
open DwordCode DwordLayout DwordEffects

/-- Byte-image carriers use the existing bare 32-bit encodings. Actual DWORD
execution below uses the caller's mode, including long-mode RIP and RAX. -/
@[expose] def firstCode (mode : Mode) (layout : Layout) : Native.Form .x86 :=
  .memory .exchangeAcc (firstDisp mode layout)
@[expose] def secondCode (mode : Mode) (layout : Layout) : Native.Form .x86 :=
  match mode with
  | .x86 => .moffs (Arithmetic.encodeNat .x86 layout.destination)
  | .x64 => .memory .storeAcc (secondDisp .x64 layout)
@[expose] def thirdCode (mode : Mode) (layout : Layout) : Native.Form .x86 :=
  .memory .exchangeAcc (thirdDisp mode layout)
@[expose] def packets (mode : Mode) (layout : Layout) : List (ControlImage.Packet .x86) :=
  [.fixed (firstCode mode layout),.fixed (secondCode mode layout),.fixed (thirdCode mode layout)]
@[expose] def entries (mode : Mode) (layout : Layout) : List (ControlImage.Entry .x86) :=
  [⟨layout.start,.fixed (firstCode mode layout)⟩,
   ⟨secondPC mode layout,.fixed (secondCode mode layout)⟩,
   ⟨thirdPC mode layout,.fixed (thirdCode mode layout)⟩]
@[expose] def Intact (mode : Mode) (layout : Layout) (memory : ByteMemory.Memory) : Prop :=
  ControlImage.Intact .x86 (entries mode layout) memory
@[expose] def image (mode : Mode) (layout : Layout) (backing : ByteMemory.Memory) : ByteMemory.Memory :=
  ControlImage.image .x86 (entries mode layout) backing

theorem byte_bindings (mode : Mode) (layout : Layout) :
    DwordCode.encode mode (first mode layout) = Native.encode .x86 (firstCode mode layout) ∧
      DwordCode.encode mode (second mode layout) = Native.encode .x86 (secondCode mode layout) ∧
      DwordCode.encode mode (third mode layout) = Native.encode .x86 (thirdCode mode layout) := by
  cases mode <;> exact ⟨rfl,rfl,rfl⟩

theorem placed_entries (mode : Mode) (layout : Layout) :
    ControlPacking.place .x86 layout.start (packets mode layout) = entries mode layout := by
  cases mode <;> rfl

theorem size_span (mode : Mode) (layout : Layout) :
    ControlPacking.size .x86 (packets mode layout) = span mode := by cases mode <;> rfl

theorem separated (mode : Mode) (layout : Layout) : ControlImage.Separated .x86 (entries mode layout) := by
  rw [←placed_entries]
  exact ControlPacking.placed_separated .x86 _ _

theorem initial_intact (mode : Mode) (layout : Layout) (backing : ByteMemory.Memory) :
    Intact mode layout (image mode layout backing) :=
  ControlImage.initialized_intact .x86 _ backing (separated mode layout)

theorem packet_bounds (mode : Mode) (layout : Layout) (entry : ControlImage.Entry .x86)
    (member : entry ∈ entries mode layout) :
    layout.start ≤ entry.pc ∧ entry.pc + (entry.bytes .x86).length ≤ endPC mode layout := by
  rw [←placed_entries] at member
  have upper := ControlPacking.placed_upper .x86 _ layout.start entry member
  rw [size_span,←endpoint] at upper
  exact ⟨ControlPacking.placed_lower .x86 _ layout.start entry member,upper⟩

theorem intact_put (mode : Mode) (layout : Layout) (memory : ByteMemory.Memory)
    (intact : Intact mode layout memory) (field : Nat) (value : Dword)
    (outside : field+4 ≤ layout.start ∨ endPC mode layout ≤ field) :
    Intact mode layout (put memory field value) := by
  intro entry member
  have bounds := packet_bounds mode layout entry member
  have framed := ByteMemory.bytes_at_frame memory field (LittleEndian.wordEncode 4 value)
    entry.pc (entry.bytes .x86).length (by
      intro index
      have small := index.isLt
      simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
      rcases outside with before | after <;> omega)
  have original := intact entry member
  change List.Mem entry [⟨layout.start,.fixed (firstCode mode layout)⟩,
    ⟨secondPC mode layout,.fixed (secondCode mode layout)⟩,
    ⟨thirdPC mode layout,.fixed (thirdCode mode layout)⟩] at member
  cases member with
  | head =>
    simpa only [ControlImage.Entry.bytes,ControlImage.Packet.bytes,ControlImage.PacketIntact,put]
      using framed.trans original
  | tail _ rest =>
    cases rest with
    | head =>
      simpa only [ControlImage.Entry.bytes,ControlImage.Packet.bytes,ControlImage.PacketIntact,put]
        using framed.trans original
    | tail _ last =>
      cases last with
      | head =>
        simpa only [ControlImage.Entry.bytes,ControlImage.Packet.bytes,ControlImage.PacketIntact,put]
          using framed.trans original
      | tail _ empty => cases empty

theorem swapped_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout state.memory) :
    Intact mode layout (swapped mode layout state).memory := by
  rw [first_effect mode layout valid state entry]
  exact intact_put mode layout state.memory intact layout.source _ valid.sourceOutside

theorem stored_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout state.memory) :
    Intact mode layout (stored mode layout state).memory := by
  rw [stored,second_effect mode layout valid _ (swapped_pc mode layout valid state entry)]
  exact intact_put mode layout (swapped mode layout state).memory
    (swapped_intact mode layout valid state entry intact) layout.destination _ valid.destinationOutside

theorem finish_intact (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout state.memory) :
    Intact mode layout (finish mode layout state).memory := by
  rw [effect mode layout valid state entry]
  exact intact_put mode layout state.memory intact layout.destination _ valid.destinationOutside

theorem first_fetch (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (location : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout state.memory) :
    fetch mode state.memory state.pc.toNat = some (first mode layout) := by
  have current := intact ⟨layout.start,.fixed (firstCode mode layout)⟩ (List.Mem.head _)
  change ByteMemory.bytesAt state.memory layout.start (Native.encode .x86 (firstCode mode layout)).length =
    Native.encode .x86 (firstCode mode layout) at current
  rw [←(byte_bindings mode layout).1] at current
  rw [location,Arithmetic.encode_nat_toNat mode layout.start (by
    have bound := valid.codeFits
    unfold endPC thirdPC secondPC at bound
    omega)]
  exact fetch_encoding mode state.memory layout.start _ current

theorem second_fetch (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (location : state.pc = Arithmetic.encodeNat mode (secondPC mode layout))
    (intact : Intact mode layout state.memory) :
    fetch mode state.memory state.pc.toNat = some (second mode layout) := by
  have current := intact ⟨secondPC mode layout,.fixed (secondCode mode layout)⟩ (List.Mem.tail _ (List.Mem.head _))
  change ByteMemory.bytesAt state.memory (secondPC mode layout) (Native.encode .x86 (secondCode mode layout)).length =
    Native.encode .x86 (secondCode mode layout) at current
  rw [←(byte_bindings mode layout).2.1] at current
  rw [location,Arithmetic.encode_nat_toNat mode (secondPC mode layout) (by
    have bound := valid.codeFits
    unfold endPC thirdPC at bound
    omega)]
  exact fetch_encoding mode state.memory _ _ current

theorem third_fetch (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (location : state.pc = Arithmetic.encodeNat mode (thirdPC mode layout))
    (intact : Intact mode layout state.memory) :
    fetch mode state.memory state.pc.toNat = some (third mode layout) := by
  have current := intact ⟨thirdPC mode layout,.fixed (thirdCode mode layout)⟩
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  change ByteMemory.bytesAt state.memory (thirdPC mode layout) (Native.encode .x86 (thirdCode mode layout)).length =
    Native.encode .x86 (thirdCode mode layout) at current
  rw [←(byte_bindings mode layout).2.2] at current
  rw [location,Arithmetic.encode_nat_toNat mode (thirdPC mode layout) (by
    have bound := valid.codeFits
    unfold endPC at bound
    omega)]
  exact fetch_encoding mode state.memory _ _ current

/-- All future fetches follow from the initial current image and exact byte
frames. Loads retain natural addresses above 4GiB in the long-mode case. -/
theorem trace (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout state.memory) :
    DwordCode.Trace mode state (program mode layout) (finish mode layout state) := by
  have a := first_fetch mode layout valid state entry intact
  have b := second_fetch mode layout valid (swapped mode layout state)
    (swapped_pc mode layout valid state entry) (swapped_intact mode layout valid state entry intact)
  have c := third_fetch mode layout valid (stored mode layout state)
    (stored_pc mode layout valid state entry) (stored_intact mode layout valid state entry intact)
  exact .step a (.step b (.step c (.nil _)))

theorem supported_run (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (owned : Nat → Prop) (sourceOwned : owned layout.source) (destinationOwned : owned layout.destination) :
    OwnedRun mode owned (program mode layout) state := by
  change owned (address mode (first mode layout) state).toNat ∧
    owned (address mode (second mode layout) (swapped mode layout state)).toNat ∧
    owned (address mode (third mode layout) (stored mode layout state)).toNat ∧ True
  rw [first_hits mode layout valid state entry,
    second_hits mode layout valid _ (swapped_pc mode layout valid state entry),
    third_hits mode layout valid _ (stored_pc mode layout valid state entry),
    source_toNat mode layout valid,destination_toNat mode layout valid]
  exact ⟨sourceOwned,destinationOwned,sourceOwned,trivial⟩

theorem correct (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout state.memory) :
    DwordCode.Trace mode state (program mode layout) (finish mode layout state) ∧
    finish mode layout state =
      { state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        accumulator := lift mode (low mode state.accumulator)
        memory := put state.memory layout.destination (get state.memory layout.source) } ∧
    Intact mode layout (finish mode layout state).memory :=
  ⟨trace mode layout valid state entry intact,effect mode layout valid state entry,
    finish_intact mode layout valid state entry intact⟩

theorem original_correct (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (backing : ByteMemory.Memory) (initialized : state.memory = image mode layout backing) :
    DwordCode.Trace mode state (program mode layout) (finish mode layout state) ∧
    finish mode layout state =
      { state with
        pc := Arithmetic.encodeNat mode (endPC mode layout)
        accumulator := lift mode (low mode state.accumulator)
        memory := put state.memory layout.destination (get state.memory layout.source) } ∧
    Intact mode layout (finish mode layout state).memory := by
  apply correct mode layout valid state entry
  rw [initialized]
  exact initial_intact mode layout backing


theorem image_frame (mode : Mode) (layout : Layout) (backing : ByteMemory.Memory) (position : Nat)
    (outside : position < layout.start ∨ endPC mode layout ≤ position) :
    image mode layout backing position = backing position := by
  unfold image
  rw [←placed_entries]
  apply ControlPacking.image_frame
  rwa [size_span,←endpoint]

theorem initial_field (mode : Mode) (layout : Layout) (backing : ByteMemory.Memory) (field : Nat)
    (outside : field+4 ≤ layout.start ∨ endPC mode layout ≤ field) :
    get (image mode layout backing) field = get backing field := by
  have equal : ByteMemory.bytesAt (image mode layout backing) field 4 = ByteMemory.bytesAt backing field 4 := by
    change List.ofFn (fun index : Fin 4 => image mode layout backing (field+index.val)) =
      List.ofFn (fun index : Fin 4 => backing (field+index.val))
    apply congrArg List.ofFn
    funext index
    apply image_frame
    have small := index.isLt
    rcases outside with before | after
    · left; omega
    · right; omega
  exact congrArg (fun bytes => BitVec.ofNat 32 (LittleEndian.pack bytes)) equal

end SmcTuring.Native.DwordImage

module
public import SmcTuring.Native.DwordTemplateCollection
public import SmcTuring.Native.DwordImage

public section
namespace SmcTuring.Native.MixedFixedTemplates

/-- A complete fixed helper packet at its original static boundary. -/
structure Entry (mode : Mode) where
  pc : Nat
  form : MixedDword.Form mode

@[expose] def span (mode : Mode) (entry : Entry mode) := (MixedDword.encode mode entry.form).length
@[expose] def Intact (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory) : Prop :=
  ByteMemory.bytesAt memory entry.pc (span mode entry)=MixedDword.encode mode entry.form
@[expose] def All (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory) : Prop :=
  ∀ entry∈entries,Intact mode entry memory
@[expose] def Outside (mode : Mode) (entry : Entry mode) (address count : Nat) : Prop :=
  address+count≤entry.pc ∨ entry.pc+span mode entry≤address
@[expose] def OutsideAll (mode : Mode) (entries : List (Entry mode)) (address count : Nat) : Prop :=
  ∀ entry∈entries,Outside mode entry address count
@[expose] def Decodes (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory) : Prop :=
  StringStack.fetch mode memory entry.pc=
    some (StringStoreWrites.liftDword mode (StringMixed.canonical mode entry.form))

theorem decodes (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory)
    (intact : Intact mode entry memory) : Decodes mode entry memory :=
  StringStack.previous_fetch mode memory entry.pc _
    (StringControl.previous_fetch mode memory entry.pc _
      (StringMixed.fetched mode memory entry.pc _ (MixedDword.current_encoding mode _ _ _ intact)))

theorem frame (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List LittleEndian.Byte) (intact : Intact mode entry memory)
    (outside : Outside mode entry address packet.length) :
    Intact mode entry (ByteMemory.putBytes memory address packet) := by
  rw [Intact,ByteMemory.bytes_at_frame]
  · exact intact
  · intro index inside
    have bound := index.isLt
    unfold ByteMemory.Inside at inside
    rcases outside with before | after <;> omega

theorem store_all (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List LittleEndian.Byte) (intact : All mode entries memory)
    (outside : OutsideAll mode entries address packet.length) :
    All mode entries (ByteMemory.putBytes memory address packet) :=
  fun entry member => frame mode entry memory address packet (intact entry member) (outside entry member)

theorem execute (mode : Mode) (entries : List (Entry mode)) (form : MixedDword.Form mode)
    (state : StringExecution.State mode) (intact : All mode entries state.principal.memory)
    (outside : OutsideAll mode entries (MixedDword.address mode form state.principal).toNat (MixedDword.width mode form)) :
    All mode entries (StringStack.execute mode
      (StringStoreWrites.liftDword mode (StringMixed.canonical mode form)) state).principal.memory := by
  rw [StringWrites.execute_memory]
  apply store_all mode entries state.principal.memory _ _ intact
  simpa only [StringMixedWrites.address,StringMixedWrites.length] using outside

theorem all_states (mode : Mode) (entries : List (Entry mode)) (forms : List (MixedDword.Form mode))
    (state : StringExecution.State mode) (intact : All mode entries state.principal.memory)
    (owned : MixedDword.OwnedRun mode (OutsideAll mode entries) forms state.principal) :
    StringTemplateStates.Run mode (fun current => All mode entries current.principal.memory)
      ((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state := by
  induction forms generalizing state with
  | nil => exact intact
  | cons form rest ih =>
    have kept := execute mode entries form state intact owned.1
    constructor
    · exact intact
    · change StringTemplateStates.Run mode _ _ (StringDword.execute mode (StringMixed.canonical mode form) state)
      change All mode entries (StringDword.execute mode (StringMixed.canonical mode form) state).principal.memory at kept
      rw [StringMixed.execute] at kept ⊢
      exact ih _ kept owned.2

theorem all_decodes (mode : Mode) (entries : List (Entry mode)) (forms : List (MixedDword.Form mode))
    (state : StringExecution.State mode) (intact : All mode entries state.principal.memory)
    (owned : MixedDword.OwnedRun mode (OutsideAll mode entries) forms state.principal) :
    StringTemplateStates.Run mode (fun current => ∀ entry∈entries,Decodes mode entry current.principal.memory)
      ((forms.map (StringMixed.canonical mode)).map (StringStoreWrites.liftDword mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun current all entry member => decodes mode entry current.principal.memory (all entry member))
    (all_states mode entries forms state intact owned)

@[expose] def copyEntries (mode : Mode) (layout : DwordLayout.Layout) : List (Entry mode) :=
  [⟨layout.start,.copy (DwordLayout.first mode layout)⟩,
   ⟨DwordLayout.secondPC mode layout,.copy (DwordLayout.second mode layout)⟩,
   ⟨DwordLayout.thirdPC mode layout,.copy (DwordLayout.third mode layout)⟩]

theorem copy_bounds (mode : Mode) (layout : DwordLayout.Layout) (entry : Entry mode)
    (member : entry∈copyEntries mode layout) :
    layout.start≤entry.pc ∧ entry.pc+span mode entry≤DwordLayout.endPC mode layout := by
  simp only [copyEntries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> cases mode <;>
    simp [span,MixedDword.encode_length,MixedDword.length,DwordCode.length,DwordLayout.first,DwordLayout.second,DwordLayout.third,
      DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,DwordLayout.storeSize,Mode.wordBytes] <;> omega

theorem copy_initial (mode : Mode) (layout : DwordLayout.Layout) (memory : ByteMemory.Memory)
    (intact : DwordImage.Intact mode layout memory) : All mode (copyEntries mode layout) memory := by
  intro entry member
  simp only [copyEntries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · have packet := intact ⟨layout.start,.fixed (DwordImage.firstCode mode layout)⟩ (List.Mem.head _)
    change ByteMemory.bytesAt memory layout.start (Native.encode .x86 (DwordImage.firstCode mode layout)).length=
      Native.encode .x86 (DwordImage.firstCode mode layout) at packet
    rw [←(DwordImage.byte_bindings mode layout).1] at packet
    exact packet
  · have packet := intact ⟨DwordLayout.secondPC mode layout,.fixed (DwordImage.secondCode mode layout)⟩
      (List.Mem.tail _ (List.Mem.head _))
    change ByteMemory.bytesAt memory (DwordLayout.secondPC mode layout)
      (Native.encode .x86 (DwordImage.secondCode mode layout)).length=
      Native.encode .x86 (DwordImage.secondCode mode layout) at packet
    rw [←(DwordImage.byte_bindings mode layout).2.1] at packet
    exact packet
  · have packet := intact ⟨DwordLayout.thirdPC mode layout,.fixed (DwordImage.thirdCode mode layout)⟩
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    change ByteMemory.bytesAt memory (DwordLayout.thirdPC mode layout)
      (Native.encode .x86 (DwordImage.thirdCode mode layout)).length=
      Native.encode .x86 (DwordImage.thirdCode mode layout) at packet
    rw [←(DwordImage.byte_bindings mode layout).2.2] at packet
    exact packet

end SmcTuring.Native.MixedFixedTemplates

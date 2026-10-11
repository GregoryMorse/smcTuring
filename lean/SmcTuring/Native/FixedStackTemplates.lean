module
public import SmcTuring.Native.StringStoreTemplateRuns

public section
namespace SmcTuring.Native.FixedStackTemplates

inductive Instruction (mode : Mode) where
  | string (form : StringForm.Form mode)
  | addSmall (displacement : BitVec 32) (value : LittleEndian.Byte)
structure Entry (mode : Mode) where
  pc : Nat
  instruction : Instruction mode
@[expose] def form (mode : Mode) : Instruction mode → StringStack.Form mode
  | .string raw => StringWrites.liftString mode raw
  | .addSmall displacement value => .addSmall displacement value
@[expose] def encode (mode : Mode) : Instruction mode → List LittleEndian.Byte
  | .string raw => StringForm.encode mode raw
  | .addSmall displacement value => WordAddImmediate.encode mode displacement value
@[expose] def Legal (mode : Mode) : Instruction mode → Prop
  | .string raw => StringForm.Legal mode raw
  | .addSmall _ _ => True
@[expose] def native (mode : Mode) (raw : Native.Form mode) : Instruction mode := .string (.native raw)
@[expose] def Intact (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory) : Prop :=
  ByteMemory.bytesAt memory entry.pc (encode mode entry.instruction).length=encode mode entry.instruction
@[expose] def All (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory) : Prop :=
  ∀ entry∈entries,Intact mode entry memory
@[expose] def Decodes (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory) : Prop :=
  StringStack.fetch mode memory entry.pc=some (form mode entry.instruction)
@[expose] def OutsideAll (mode : Mode) (entries : List (Entry mode)) (address count : Nat) : Prop :=
  ∀ entry∈entries,address+count≤entry.pc ∨ entry.pc+(encode mode entry.instruction).length≤address

theorem decodes (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory)
    (legal : Legal mode entry.instruction) (intact : Intact mode entry memory) : Decodes mode entry memory := by
  cases entry with
  | mk pc instruction =>
    cases instruction with
    | string raw =>
      exact StringEncodedTemplates.string_fetch mode memory pc raw
        (StringForm.fetch_current_encoding mode memory pc raw legal intact)
    | addSmall displacement value => exact StringStack.add_encoding mode memory pc displacement value intact

theorem frame (mode : Mode) (entry : Entry mode) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (intact : Intact mode entry memory)
    (outside : address+packet.length≤entry.pc ∨ entry.pc+(encode mode entry.instruction).length≤address) :
    Intact mode entry (ByteMemory.putBytes memory address packet) := by
  rw [Intact,ByteMemory.bytes_at_frame]
  · exact intact
  · intro index inside
    have bound:=index.isLt
    unfold ByteMemory.Inside at inside
    rcases outside with before | after <;> omega

theorem store_all (mode : Mode) (entries : List (Entry mode)) (memory : ByteMemory.Memory) (address : Nat) (packet : List LittleEndian.Byte)
    (initial : All mode entries memory) (outside : OutsideAll mode entries address packet.length) :
    All mode entries (ByteMemory.putBytes memory address packet) :=
  fun entry member => frame mode entry memory address packet (initial entry member) (outside entry member)

theorem all_states (mode : Mode) (entries : List (Entry mode)) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode) (initial : All mode entries state.principal.memory)
    (regions : StringStoreRegions.Run mode (OutsideAll mode entries) forms state) :
    StringTemplateStates.Run mode (fun reached => All mode entries reached.principal.memory) forms state :=
  StringStoreTemplateRuns.preserve mode (OutsideAll mode entries) (All mode entries) forms state initial
    (store_all mode entries) regions

theorem all_decodes (mode : Mode) (entries : List (Entry mode)) (forms : List (StringStack.Form mode))
    (legal : ∀ entry∈entries,Legal mode entry.instruction) (state : StringExecution.State mode)
    (initial : All mode entries state.principal.memory)
    (regions : StringStoreRegions.Run mode (OutsideAll mode entries) forms state) :
    StringTemplateStates.Run mode (fun reached => ∀ entry∈entries,Decodes mode entry reached.principal.memory) forms state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun reached intact entry member => decodes mode entry reached.principal.memory (legal entry member) (intact entry member))
    (all_states mode entries forms state initial regions)

@[expose] def place (mode : Mode) : Nat → List (Instruction mode) → List (Entry mode)
  | _,[] => []
  | pc,instruction::rest => ⟨pc,instruction⟩::place mode (pc+(encode mode instruction).length) rest
@[expose] def bytes (mode : Mode) (instructions : List (Instruction mode)) := instructions.flatMap (encode mode)

theorem placed_initial (mode : Mode) (pc : Nat) (instructions : List (Instruction mode)) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory pc (bytes mode instructions).length=bytes mode instructions) :
    All mode (place mode pc instructions) memory := by
  induction instructions generalizing pc with
  | nil => simp [All,place]
  | cons instruction rest ih =>
    have first:=StringWindow.packet_window memory pc [] (encode mode instruction) (bytes mode rest)
      (by simpa only [bytes,List.flatMap_cons,List.nil_append] using current)
    have later:=StringWindow.packet_window memory pc (encode mode instruction) (bytes mode rest) []
      (by simpa only [bytes,List.flatMap_cons,List.append_nil] using current)
    have tail:=ih _ later
    intro entry member
    rcases List.mem_cons.mp member with rfl | inside
    · exact first
    · exact tail entry inside

theorem placed_bounds (mode : Mode) (pc : Nat) (instructions : List (Instruction mode))
    (entry : Entry mode) (member : entry∈place mode pc instructions) :
    pc≤entry.pc ∧ entry.pc+(encode mode entry.instruction).length≤pc+(bytes mode instructions).length := by
  induction instructions generalizing pc with
  | nil => simp [place] at member
  | cons instruction rest ih =>
    rcases List.mem_cons.mp member with rfl | inside
    · simp only [bytes,List.flatMap_cons,List.length_append];omega
    · have tail:=ih _ inside
      simp only [bytes,List.flatMap_cons,List.length_append] at tail ⊢
      omega

theorem placed_count (mode : Mode) (pc : Nat) (instructions : List (Instruction mode)) :
    (place mode pc instructions).length=instructions.length := by
  induction instructions generalizing pc with
  | nil => rfl
  | cons instruction rest ih => simp only [place,List.length_cons,ih]

theorem placed_legal (mode : Mode) (pc : Nat) (instructions : List (Instruction mode))
    (legal : ∀ instruction∈instructions,Legal mode instruction) :
    ∀ entry∈place mode pc instructions,Legal mode entry.instruction := by
  induction instructions generalizing pc with
  | nil => simp [place]
  | cons instruction rest ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | inside
    · exact legal instruction (List.Mem.head _)
    · exact ih _ (fun item belongs => legal item (List.Mem.tail _ belongs)) entry inside

end SmcTuring.Native.FixedStackTemplates

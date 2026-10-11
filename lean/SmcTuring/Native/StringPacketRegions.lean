module
public import SmcTuring.Native.StringMacroTemplates
public import SmcTuring.Native.StringTemplateStates

public section
namespace SmcTuring.Native.StringPacketRegions
open StringMacroLayout

@[expose] def Within (packet : StringWrites.Packet) (start count : Nat) : Prop :=
  start≤packet.address ∧ packet.address+packet.bytes.length≤start+count

/-- Complete architectural windows, in either cursor operand or either
separate buffer envelope. Values and future native states are not inputs. -/
@[expose] def Allowed (mode : Mode) (p : Params) (packet : StringWrites.Packet) : Prop :=
  Within packet (StringCodec.sourceField mode p.start) mode.wordBytes ∨
  Within packet (StringCodec.destinationField mode p.start) mode.wordBytes ∨
  Within packet p.source (max p.size mode.wordBytes) ∨
  Within packet p.destination (max p.size mode.wordBytes)

@[expose] def WordAllowed (mode : Mode) (p : Params) (address : Word mode) : Prop :=
  address.toNat=StringCodec.sourceField mode p.start ∨
  address.toNat=StringCodec.destinationField mode p.start ∨
  address.toNat=p.source ∨ address.toNat=p.destination

@[expose] def Run (mode : Mode) (p : Params) : List (StringStack.Form mode) → StringExecution.State mode → Prop
  | [],_ => True
  | form::rest,state => Allowed mode p (StringWrites.packet mode form state) ∧
      Run mode p rest (StringStack.execute mode form state)

theorem append (mode : Mode) (p : Params) (first second : List (StringStack.Form mode))
    (state : StringExecution.State mode) :
    Run mode p (first++second) state ↔ Run mode p first state ∧ Run mode p second (StringWrites.run mode first state) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append,Run,StringWrites.run,true_and]
  | cons form rest ih => simp only [List.cons_append,Run,StringWrites.run,ih,and_assoc]

theorem word_packet (mode : Mode) (p : Params) (address : Word mode) (value : Word mode)
    (owned : WordAllowed mode p address) :
    Allowed mode p ⟨address.toNat,LittleEndian.wordEncode mode.wordBytes value⟩ := by
  simp only [WordAllowed] at owned
  simp only [Allowed,Within,LittleEndian.word_encode_length]
  rcases owned with a | b | c | d
  · exact Or.inl ⟨by omega,by omega⟩
  · exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega,by omega⟩))

theorem native_run (mode : Mode) (p : Params) (forms : List (Native.Form mode)) (state : StringExecution.State mode)
    (owned : Writes.OwnedRun mode (WordAllowed mode p) forms state.principal) :
    Run mode p (forms.map (StringWrites.liftNative mode)) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    exact ⟨word_packet mode p _ _ owned.1,
      ih (StringStack.execute mode (StringWrites.liftNative mode form) state) owned.2⟩

theorem interval_run (mode : Mode) (p : Params) (start stop : Nat)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (covers : ∀ packet : StringWrites.Packet, start≤packet.address → packet.address+packet.bytes.length≤stop → Allowed mode p packet)
    (owned : StringWrites.OwnedRun mode start stop forms state) : Run mode p forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih => exact ⟨covers _ owned.1.2.1 owned.1.2.2,ih _ owned.2⟩

theorem execute_intact (mode : Mode) (p : Params) (state : StringExecution.State mode)
    (form : StringStack.Form mode) (intact : StringMacroTemplates.Intact mode p state.principal.memory)
    (sourceOutside : Outside mode p p.source) (destinationOutside : Outside mode p p.destination)
    (allowed : Allowed mode p (StringWrites.packet mode form state)) :
    StringMacroTemplates.Intact mode p (StringStack.execute mode form state).principal.memory := by
  rw [StringWrites.execute_memory]
  rcases allowed with a | b | c | d
  · exact StringMacroTemplates.operand_store mode p _ _ _ intact (Or.inl a)
  · exact StringMacroTemplates.operand_store mode p _ _ _ intact (Or.inr b)
  · exact StringMacroTemplates.buffer_store mode p _ p.source _ _ intact sourceOutside c
  · exact StringMacroTemplates.buffer_store mode p _ p.destination _ _ intact destinationOutside d

/-- This bridges proved actual store regions to the property at every
intermediate state, including the endpoint and all stores inside readers. -/
theorem all_states (mode : Mode) (p : Params) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode) (intact : StringMacroTemplates.Intact mode p state.principal.memory)
    (sourceOutside : Outside mode p p.source) (destinationOutside : Outside mode p p.destination)
    (regions : Run mode p forms state) :
    StringTemplateStates.Run mode (fun current => StringMacroTemplates.Intact mode p current.principal.memory) forms state := by
  induction forms generalizing state with
  | nil => exact intact
  | cons form rest ih =>
    exact ⟨intact,ih _ (execute_intact mode p state form intact sourceOutside destinationOutside regions.1) regions.2⟩

end SmcTuring.Native.StringPacketRegions

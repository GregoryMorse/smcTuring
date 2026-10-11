module
public import SmcTuring.Native.StringEncodedTemplates

public section
namespace SmcTuring.Native.StringMacroCrossTemplates
open StringMacroLayout

/-- Separate code and buffer envelopes ensure a writer never touches the
other macro's fixed executable bytes. This adds no execution premise. -/
structure Separate (mode : Mode) (writer observed : Params) : Prop where
  code : endpoint mode writer≤observed.start ∨ endpoint mode observed≤writer.start
  source : writer.source+max writer.size mode.wordBytes≤observed.start ∨ endpoint mode observed≤writer.source
  destination : writer.destination+max writer.size mode.wordBytes≤observed.start ∨ endpoint mode observed≤writer.destination

theorem outside (mode : Mode) (writer observed : Params) (separate : Separate mode writer observed)
    (packet : StringWrites.Packet) (allowed : StringPacketRegions.Allowed mode writer packet) :
    packet.address+packet.bytes.length≤observed.start ∨ endpoint mode observed≤packet.address := by
  have coordinates:=field_coordinates mode writer
  unfold StringPacketRegions.Allowed StringPacketRegions.Within at allowed
  rcases allowed with sourceField | destinationField | source | destination
  · rcases separate.code with before | after <;> omega
  · rcases separate.code with before | after <;> omega
  · rcases separate.source with before | after <;> omega
  · rcases separate.destination with before | after <;> omega

theorem execute (mode : Mode) (writer observed : Params) (separate : Separate mode writer observed)
    (form : StringStack.Form mode) (state : StringExecution.State mode)
    (current : StringMacroTemplates.Intact mode observed state.principal.memory)
    (allowed : StringPacketRegions.Allowed mode writer (StringWrites.packet mode form state)) :
    StringMacroTemplates.Intact mode observed (StringStack.execute mode form state).principal.memory := by
  rw [StringWrites.execute_memory]
  exact StringMacroTemplates.frame mode observed _ _ _ current (outside mode writer observed separate _ allowed)

theorem all_states (mode : Mode) (writer observed : Params) (separate : Separate mode writer observed)
    (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (current : StringMacroTemplates.Intact mode observed state.principal.memory)
    (regions : StringPacketRegions.Run mode writer forms state) :
    StringTemplateStates.Run mode (fun reached => StringMacroTemplates.Intact mode observed reached.principal.memory) forms state := by
  induction forms generalizing state with
  | nil => exact current
  | cons form rest ih => exact ⟨current,ih _ (execute mode writer observed separate form state current regions.1) regions.2⟩

theorem all_decodes (mode : Mode) (writer observed : Params) (separate : Separate mode writer observed)
    (sizeFits : observed.size<2^31) (forms : List (StringStack.Form mode)) (state : StringExecution.State mode)
    (current : StringMacroTemplates.Intact mode observed state.principal.memory)
    (regions : StringPacketRegions.Run mode writer forms state) :
    StringTemplateStates.Run mode (fun reached => StringEncodedTemplates.Decodes mode observed reached.principal.memory) forms state :=
  StringTemplateStates.monotone mode _ _ forms state
    (fun _ kept => StringEncodedTemplates.macro_decodes mode observed _ sizeFits kept)
    (all_states mode writer observed separate forms state current regions)

end SmcTuring.Native.StringMacroCrossTemplates

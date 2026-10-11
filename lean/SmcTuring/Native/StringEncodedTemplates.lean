module
public import SmcTuring.Native.StringMacroTemplateWrites

public section
namespace SmcTuring.Native.StringEncodedTemplates
open StringMacroLayout

@[expose] def encoding (mode : Mode) (forms : List (StringForm.Form mode)) : List LittleEndian.Byte :=
  (forms.map (StringForm.encode mode)).flatten
@[expose] def lengths (mode : Mode) (forms : List (StringForm.Form mode)) : List Nat :=
  forms.map (fun form => (StringForm.encode mode form).length)
@[expose] def offset (mode : Mode) (forms : List (StringForm.Form mode)) (index : Nat) : Nat :=
  (encoding mode (forms.take index)).length

theorem string_fetch (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringForm.Form mode)
    (packet : StringForm.fetch mode memory pc=some form) :
    StringStack.fetch mode memory pc=some (StringWrites.liftString mode form) :=
  StringStack.previous_fetch mode memory pc _
    (StringControl.previous_fetch mode memory pc _ (StringDword.string_fetch mode memory pc form packet))

theorem fetch_split (mode : Mode) (memory : ByteMemory.Memory) (start : Nat)
    (forms before after : List (StringForm.Form mode)) (form : StringForm.Form mode)
    (split : forms=before++form::after) (legal : StringForm.Legal mode form)
    (current : ByteMemory.bytesAt memory start (encoding mode forms).length=encoding mode forms) :
    StringStack.fetch mode memory (start+(encoding mode before).length)=some (StringWrites.liftString mode form) := by
  have arranged : encoding mode forms=encoding mode before++StringForm.encode mode form++encoding mode after := by
    rw [split]
    simp only [encoding,List.map_append,List.flatten_append,List.map_cons,List.flatten_cons,List.append_assoc]
  have packet := StringWindow.packet_window memory start (encoding mode before) (StringForm.encode mode form) (encoding mode after)
    (by rw [←arranged];exact current)
  exact string_fetch mode memory _ form (StringForm.fetch_current_encoding mode memory _ form legal packet)

theorem fetch_index (mode : Mode) (memory : ByteMemory.Memory) (start : Nat)
    (forms : List (StringForm.Form mode)) (index : Nat) (small : index<forms.length)
    (legal : ∀ form∈forms,StringForm.Legal mode form)
    (current : ByteMemory.bytesAt memory start (encoding mode forms).length=encoding mode forms) :
    StringStack.fetch mode memory (start+offset mode forms index)=some (StringWrites.liftString mode forms[index]) := by
  apply fetch_split mode memory start forms (forms.take index) (forms.drop (index+1)) forms[index]
  · have h := List.take_append_drop index forms
    rw [List.drop_eq_getElem_cons small] at h
    exact h.symm
  · exact legal _ (List.getElem_mem small)
  · exact current

theorem offset_sum (mode : Mode) (forms : List (StringForm.Form mode)) (index : Nat) :
    offset mode forms index=(lengths mode forms |>.take index).sum := by
  simp only [offset,encoding,lengths,List.length_flatten,List.map_map,Function.comp_def,List.map_take]

/-- Mutating either initializer's operand changes no static instruction
length. This binds all observed boundaries to the original packed geometry. -/
theorem macro_lengths (mode : Mode) (start source destination freshSource freshDestination size : Nat) :
    lengths mode (StringProgram.forms mode start source destination size)=
      lengths mode (StringProgram.forms mode start freshSource freshDestination size) := by
  cases mode <;> simp [lengths,StringProgram.forms,StringSetup.forms,StringSetup.sourceForms,
    StringInit.forms,StringForm.encode,Native.encode,Appendix.ByteCode.encode]

@[expose] def live (mode : Mode) (p : Params) (memory : ByteMemory.Memory) : Params :=
  {p with
    source := (Protected.wordAt mode memory (StringCodec.sourceField mode p.start)).toNat,
    destination := (Protected.wordAt mode memory (StringCodec.destinationField mode p.start)).toNat}

@[expose] def Decodes (mode : Mode) (p : Params) (memory : ByteMemory.Memory) : Prop :=
  ∀ index, index<(StringProgram.forms mode p.start p.source p.destination p.size).length →
    ∃ form, StringForm.Legal mode form ∧
      StringStack.fetch mode memory
        (p.start+offset mode (StringProgram.forms mode p.start p.source p.destination p.size) index)=
        some (StringWrites.liftString mode form)

theorem macro_decodes (mode : Mode) (p : Params) (memory : ByteMemory.Memory)
    (sizeFits : p.size<2^31) (intact : StringMacroTemplates.Intact mode p memory) : Decodes mode p memory := by
  intro index small
  let original := StringProgram.forms mode p.start p.source p.destination p.size
  let currentForms := StringProgram.forms mode p.start (live mode p memory).source (live mode p memory).destination p.size
  have sameLengths : lengths mode original=lengths mode currentForms := macro_lengths mode _ _ _ _ _ _
  have sameCount : original.length=currentForms.length := by
    have h := congrArg List.length sameLengths
    simpa only [lengths,List.length_map] using h
  have currentSmall : index<currentForms.length := by rw [←sameCount];exact small
  have current : ByteMemory.bytesAt memory p.start (encoding mode currentForms).length=encoding mode currentForms := by
    have h := StringMacroTemplates.current mode p memory intact
    simpa only [currentForms,encoding,StringProgram.encoding mode _ _ _ _ sizeFits,live,bytes] using h
  have packet := fetch_index mode memory p.start currentForms index currentSmall
    (StringProgram.legal mode _ _ _ _ ) current
  have sameOffset : offset mode original index=offset mode currentForms index := by
    simp only [offset_sum,sameLengths]
  refine ⟨currentForms[index],StringProgram.legal mode _ _ _ _ _ (List.getElem_mem currentSmall),?_⟩
  rw [←sameOffset] at packet
  exact packet

/-- Every statically emitted instruction boundary remains decodable at
every actual reached prefix, including all initializer and restore stores. -/
theorem all_states (mode : Mode) (p : Params) (state : StringExecution.State mode) (ready : Ready mode p state) :
    StringTemplateStates.Run mode (fun current => Decodes mode p current.principal.memory)
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state :=
  StringTemplateStates.monotone mode _ _ _ state
    (fun current intact => macro_decodes mode p current.principal.memory ready.sizeFits intact)
    (StringMacroTemplateWrites.templates mode p state ready)

theorem at_prefix (mode : Mode) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (before after : List (StringStack.Form mode))
    (cut : (StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)=before++after) :
    Decodes mode p (StringWrites.run mode before state).principal.memory := by
  have states := all_states mode p state ready
  rw [cut] at states
  exact StringTemplateStates.at_prefix mode _ before after state states

end SmcTuring.Native.StringEncodedTemplates

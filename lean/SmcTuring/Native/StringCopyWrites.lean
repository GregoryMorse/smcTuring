module
public import SmcTuring.Native.StringDwordWritesBridge
public import SmcTuring.Native.StringFieldWrites
public import SmcTuring.Native.StringDwordCopy
public import SmcTuring.Native.ConversionOwnership

public section
namespace SmcTuring.Native.StringCopyWrites

theorem copy_address (mode : Mode) (form : DwordCode.Form mode) (state : StringExecution.State mode) :
    (StringWrites.packet mode (StringStoreWrites.liftDword mode (StringDwordCopy.copy mode form)) state).address=
      (DwordCode.address mode form state.principal).toNat := by
  cases mode <;> cases form <;> rfl

theorem copy_length (mode : Mode) (form : DwordCode.Form mode) (state : StringExecution.State mode) :
    (StringWrites.packet mode (StringStoreWrites.liftDword mode (StringDwordCopy.copy mode form)) state).bytes.length=4 := by
  cases mode <;> cases form <;> exact LittleEndian.word_encode_length _ _

theorem copy_write (mode : Mode) (codeStart codeEnd : Nat) (form : DwordCode.Form mode) (state : StringExecution.State mode)
    (inside : codeStart≤(DwordCode.address mode form state.principal).toNat ∧ (DwordCode.address mode form state.principal).toNat+4≤codeEnd) :
    StringWrites.CodeWrite mode codeStart codeEnd (StringStoreWrites.liftDword mode (StringDwordCopy.copy mode form)) state := by
  unfold StringWrites.CodeWrite
  rw [copy_address,copy_length]
  exact ⟨by decide,inside⟩

theorem copy_run (mode : Mode) (codeStart codeEnd : Nat) (forms : List (DwordCode.Form mode)) (state : StringExecution.State mode)
    (owned : DwordCode.OwnedRun mode (fun address => codeStart≤address ∧ address+4≤codeEnd) forms state.principal) :
    StringWrites.OwnedRun mode codeStart codeEnd ((forms.map (StringDwordCopy.copy mode)).map (StringStoreWrites.liftDword mode)) state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form forms ih =>
    constructor
    · exact copy_write mode codeStart codeEnd form state owned.1
    · change StringWrites.OwnedRun mode codeStart codeEnd ((forms.map (StringDwordCopy.copy mode)).map (StringStoreWrites.liftDword mode))
        (StringDword.execute mode (StringDwordCopy.copy mode form) state)
      rw [StringDwordCopy.copy_execute]
      exact ih _ owned.2

theorem word (mode : Mode) (codeStart codeEnd : Nat) (layout : ConversionLayout.Layout) (valid : ConversionLayout.Admissible mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (sourceInside : codeStart≤layout.source ∧ layout.source+mode.wordBytes≤codeEnd)
    (destinationInside : codeStart≤layout.destination ∧ layout.destination+mode.wordBytes≤codeEnd) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringDwordCopy.wordProgram mode layout).map (StringStoreWrites.liftDword mode)) state := by
  have positive : 0<mode.wordBytes := by cases mode <;> decide
  have source:=StringFieldWrites.word_owned mode codeStart codeEnd layout.source (by have fits:=valid.sourceFits;omega) sourceInside
  have destination:=StringFieldWrites.word_owned mode codeStart codeEnd layout.destination (by have fits:=valid.destinationFits;omega) destinationInside
  have actual:=ConversionOwnership.supported_run mode layout valid state.principal entry (StringWrites.WordOwned mode codeStart codeEnd) source destination
  have mapped : ((StringDwordCopy.wordProgram mode layout).map (StringStoreWrites.liftDword mode))=
      (ConversionLayout.program mode layout).map (StringWrites.liftNative mode) := by rw [StringDwordCopy.wordProgram,List.map_map];rfl
  rw [mapped]
  exact StringWrites.native_owned_run mode codeStart codeEnd _ state actual

theorem dword (mode : Mode) (codeStart codeEnd : Nat) (layout : DwordLayout.Layout) (valid : DwordLayout.Admissible mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (sourceInside : codeStart≤layout.source ∧ layout.source+4≤codeEnd)
    (destinationInside : codeStart≤layout.destination ∧ layout.destination+4≤codeEnd) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringDwordCopy.dwordProgram mode layout).map (StringStoreWrites.liftDword mode)) state :=
  copy_run mode codeStart codeEnd _ state (DwordImage.supported_run mode layout valid state.principal entry _ sourceInside destinationInside)

end SmcTuring.Native.StringCopyWrites

module
public import SmcTuring.Native.StringFieldWrites
public import SmcTuring.Native.StringSetup
public import SmcTuring.Appendix.Listing9DeclarationWrites

public section
namespace SmcTuring.Appendix.Listing8SetupWrites
open Native

theorem source (mode : Mode) (codeStart codeEnd start source : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : StringCodec.bodyStart mode start<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=StringInit.bytes mode start source)
    (fieldOwned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode (StringCodec.sourceField mode start)))
    (sourceOwned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode source)) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringSetup.sourceForms mode start source).map (StringWrites.liftString mode)) state := by
  have initialFits:=(StringSetup.initializer_fits mode start fits).1
  have first:=Listing9DeclarationWrites.owned mode codeStart codeEnd start source state entry initialFits current fieldOwned sourceOwned
  have effect:=StringInit.effect mode start source state entry initialFits current
  have next : (StringExecution.run mode (StringInit.forms mode start source) state).principal.pc=Arithmetic.encodeNat mode (start+StringCodec.initialSize mode) := by rw [effect]
  have last:=StringFieldWrites.exchange mode false codeStart codeEnd (start+StringCodec.initialSize mode) (StringCodec.sourceField mode start)
    (StringExecution.run mode (StringInit.forms mode start source) state) next (StringSetup.cursor_range mode start) fieldOwned
  rw [StringSetup.sourceForms,List.map_append,StringWrites.owned_run_append,StringWrites.run_lift_string]
  exact ⟨first,last,trivial⟩

/-- Source and destination declaration targets follow from the present
initial packet bytes. Source saving derives the second current packet. -/
theorem owned (mode : Mode) (codeStart codeEnd start source destination : Nat) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (fits : StringCodec.bodyStart mode start<2^(8*mode.wordBytes))
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode)=StringInit.bytes mode start source)
    (destinationCurrent : ByteMemory.bytesAt state.principal.memory (StringCodec.destinationStart mode start) (StringCodec.initialSize mode)=
      StringInit.bytes mode (StringCodec.destinationStart mode start) destination)
    (sourceField : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode (StringCodec.sourceField mode start)))
    (destinationField : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode (StringCodec.destinationField mode start)))
    (sourceOwned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode source))
    (destinationOwned : StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode destination)) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringSetup.forms mode start source destination).map (StringWrites.liftString mode)) state := by
  have first:=Listing8SetupWrites.source mode codeStart codeEnd start source state entry fits sourceCurrent sourceField sourceOwned
  let saved:=StringExecution.run mode (StringSetup.sourceForms mode start source) state
  have savedEffect:=StringSetup.source_effect mode start source state entry fits sourceCurrent
  have savedPC : saved.principal.pc=Arithmetic.encodeNat mode (StringCodec.destinationStart mode start) := by
    dsimp only [saved];rw [savedEffect]
  have savedCurrent : ByteMemory.bytesAt saved.principal.memory (StringCodec.destinationStart mode start) (StringCodec.initialSize mode)=
      StringInit.bytes mode (StringCodec.destinationStart mode start) destination := by
    dsimp only [saved];rw [savedEffect,StringSetup.destination_window];exact destinationCurrent
  have initialFits:=(StringSetup.initializer_fits mode start fits).2
  have second:=Listing9DeclarationWrites.owned mode codeStart codeEnd (StringCodec.destinationStart mode start) destination saved
    savedPC initialFits savedCurrent destinationField destinationOwned
  have initialized:=StringInit.effect mode (StringCodec.destinationStart mode start) destination saved savedPC initialFits savedCurrent
  have next : (StringExecution.run mode (StringInit.forms mode (StringCodec.destinationStart mode start) destination) saved).principal.pc=
      Arithmetic.encodeNat mode (StringCodec.destinationStart mode start+StringCodec.initialSize mode) := by rw [initialized]
  have last:=StringFieldWrites.exchange mode true codeStart codeEnd (StringCodec.destinationStart mode start+StringCodec.initialSize mode) (StringCodec.destinationField mode start)
    (StringExecution.run mode (StringInit.forms mode (StringCodec.destinationStart mode start) destination) saved) next
    (StringSetup.cursor_range mode (StringCodec.destinationStart mode start)) destinationField
  rw [StringSetup.forms,List.map_append,List.map_append,StringWrites.owned_run_append,StringWrites.owned_run_append,StringWrites.run_append]
  simp only [StringWrites.run_lift_string]
  exact ⟨⟨first,second⟩,last,trivial⟩

end SmcTuring.Appendix.Listing8SetupWrites

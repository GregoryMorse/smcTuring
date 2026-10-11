module
public import SmcTuring.Native.StringMacroEffects
public import SmcTuring.Native.StringFieldWrites

public section
namespace SmcTuring.Appendix.Listing8MacroWriteBounds
open Native StringMacroLayout

/-- Static placement of the emitted macro and its complete code buffers.
The max covers DEFDATA's word write even when MOVS copies less than a word. -/
structure Placement (mode : Mode) (codeStart codeEnd : Nat) (p : Params) : Prop where
  code : codeStart≤p.start ∧ endpoint mode p≤codeEnd
  source : codeStart≤p.source ∧ p.source+max p.size mode.wordBytes≤codeEnd
  destination : codeStart≤p.destination ∧ p.destination+max p.size mode.wordBytes≤codeEnd

theorem fields (mode : Mode) (codeStart codeEnd : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode codeStart codeEnd p) :
    StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode (StringCodec.sourceField mode p.start)) ∧
    StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode (StringCodec.destinationField mode p.start)) := by
  have coords:=field_coordinates mode p
  have lower:=placed.code.1
  have upper:=placed.code.2
  have prefixFits:=prefix_capacity mode p state ready
  exact ⟨StringFieldWrites.word_owned mode codeStart codeEnd _ (StringSetup.source_field_fits mode p.start prefixFits) ⟨by omega,by omega⟩,
    StringFieldWrites.word_owned mode codeStart codeEnd _ (StringSetup.destination_field_fits mode p.start prefixFits) ⟨by omega,by omega⟩⟩

theorem buffers (mode : Mode) (codeStart codeEnd : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode codeStart codeEnd p) :
    StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode p.source) ∧
    StringWrites.WordOwned mode codeStart codeEnd (Arithmetic.encodeNat mode p.destination) := by
  have source:=source_capacity mode p state ready
  have destination:=destination_capacity mode p state ready
  have width:=Nat.le_max_right p.size mode.wordBytes
  have sourcePlace:=placed.source
  have destinationPlace:=placed.destination
  exact ⟨StringFieldWrites.word_owned mode codeStart codeEnd p.source source.2.2 ⟨sourcePlace.1,by omega⟩,
    StringFieldWrites.word_owned mode codeStart codeEnd p.destination destination.2.2 ⟨destinationPlace.1,by omega⟩⟩

theorem copied_bounds (mode : Mode) (codeStart codeEnd : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode codeStart codeEnd p) :
    codeStart≤(StringMacroEffects.setup mode p state).destinationIndex.toNat ∧
    (StringMacroEffects.setup mode p state).destinationIndex.toNat+(StringPlan.widths mode p.size).sum≤codeEnd := by
  have total:=StringPlan.total mode p.size
  change (StringPlan.widths mode p.size).sum=p.size at total
  have destination:=destination_capacity mode p state ready
  have place:=placed.destination
  have width:=Nat.le_max_left p.size mode.wordBytes
  rw [StringMacroEffects.setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ destination.2.2]
  change codeStart≤p.destination ∧ p.destination+(StringPlan.widths mode p.size).sum≤codeEnd
  rw [total]
  exact ⟨place.1,by omega⟩

end SmcTuring.Appendix.Listing8MacroWriteBounds

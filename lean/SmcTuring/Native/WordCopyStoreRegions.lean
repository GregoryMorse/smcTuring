module
public import SmcTuring.Native.ConversionOwnership
public import SmcTuring.Native.BoundedStoreRegions

public section
namespace SmcTuring.Native.WordCopyStoreRegions

/-- All three full-word stores use the two actual conversion operand fields.
Addresses and subsequent PCs are derived from static layout and entry. -/
theorem regions (mode : Mode) (allowed : Nat → Nat → Prop) (layout : ConversionLayout.Layout)
    (valid : ConversionLayout.Admissible mode layout) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode layout.start)
    (source : allowed layout.source mode.wordBytes) (destination : allowed layout.destination mode.wordBytes) :
    StringStoreRegions.Run mode allowed
      ((StringDwordCopy.wordProgram mode layout).map (StringStoreWrites.liftDword mode)) state := by
  have native:=ConversionOwnership.supported_run mode layout valid state.principal entry
    (fun address => allowed address.toNat mode.wordBytes)
    (by rw [ConversionLayout.source_toNat mode layout valid];exact source)
    (by rw [ConversionLayout.destination_toNat mode layout valid];exact destination)
  have lifted:=StringStoreTemplateRuns.native mode allowed _ state native
  have mapping : (fun raw => StringStoreWrites.liftDword mode (StringDwordCopy.native mode raw))=StringWrites.liftNative mode := by
    funext raw;rfl
  rw [StringDwordCopy.wordProgram,List.map_map]
  change StringStoreRegions.Run mode allowed
    ((ConversionLayout.program mode layout).map (fun raw => StringStoreWrites.liftDword mode (StringDwordCopy.native mode raw))) state
  rw [mapping]
  exact lifted

end SmcTuring.Native.WordCopyStoreRegions

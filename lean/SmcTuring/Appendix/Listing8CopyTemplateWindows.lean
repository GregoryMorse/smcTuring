module
public import SmcTuring.Native.StringMacroCopyPrefixes
public import SmcTuring.Appendix.Listing8OwnerTemplateCollection

public section
namespace SmcTuring.Appendix.Listing8CopyTemplateWindows
open Native Listing8OwnerTemplateCollection

/-- Copying keeps x86 absolute fields and x64 encoded displacements verbatim.
This descriptor proves decoding; later retargeting proves operand meaning. -/
@[expose] def relocate (mode : Mode) : Template mode → Nat → Template mode
  | .pointer source _,pc => .pointer source pc
  | .scalar _ d,pc => .scalar pc d
@[expose] def header (mode : Mode) : Template mode → Nat
  | .pointer _ _ => ReaderImage.labelOffset mode
  | .scalar _ _ => 6

theorem header_bounds (mode : Mode) (template : Template mode) :
    header mode template≤span mode template ∧ field mode template=start mode template+header mode template := by
  cases template with
  | pointer source copied => cases mode <;> simp [header,span,field,start,Listing8Prototypes.pointerSpan,
      Listing8Prototypes.pointerField,ReaderImage.labelOffset,ReaderImage.totalSize]
  | scalar pc d => exact ⟨by change 6≤10;decide,rfl⟩

/-- A completed fixed header gives a valid full template immediately, even
while its mutable operand still consists of partially copied current bytes. -/
theorem copied_header (mode : Mode) (template : Template mode) (initial backing : ByteMemory.Memory)
    (intact : Intact mode template initial) (source destination count offset : Nat)
    (located : start mode template=source+offset) (complete : offset+header mode template≤count) :
    Intact mode (relocate mode template (destination+offset))
      (ByteMemory.putBytes backing destination (ByteMemory.bytesAt initial source count)) := by
  cases template with
  | pointer origin pc =>
    change PayloadTemplate.Prefix _ (destination+offset) (Listing8PointerTemplate.fixed mode origin)
    rw [PayloadTemplate.Prefix,StringCopyPrefixes.snapshot_window]
    · rw [←located];exact intact
    · simpa only [Listing8PointerTemplate.fixed_length,header] using complete
  | scalar pc d =>
    change PayloadTemplate.Prefix _ (destination+offset) (Listing8ScalarTemplate.fixed d)
    rw [PayloadTemplate.Prefix,StringCopyPrefixes.snapshot_window]
    · rw [←located];exact intact
    · simpa only [Listing8ScalarTemplate.fixed_length,header] using complete

theorem copied_decodes (mode : Mode) (template : Template mode) (initial backing : ByteMemory.Memory)
    (intact : Intact mode template initial) (source destination count offset : Nat)
    (located : start mode template=source+offset) (complete : offset+header mode template≤count) :
    Decodes mode (relocate mode template (destination+offset))
      (ByteMemory.putBytes backing destination (ByteMemory.bytesAt initial source count)) :=
  decodes mode _ _ (copied_header mode template initial backing intact source destination count offset located complete)

/-- Templates outside the exact copied prefix retain every current static
instruction, independent of source snapshot contents. -/
theorem outside_decodes (mode : Mode) (templates : List (Template mode)) (initial backing : ByteMemory.Memory)
    (intact : All mode templates backing) (source destination count : Nat) :
    ∀ template∈templates,Outside mode template ⟨destination,ByteMemory.bytesAt initial source count⟩ →
      Intact mode template (ByteMemory.putBytes backing destination (ByteMemory.bytesAt initial source count)) ∧
      Decodes mode template (ByteMemory.putBytes backing destination (ByteMemory.bytesAt initial source count)) := by
  intro template member outside
  have kept := store_outside mode templates backing intact ⟨destination,ByteMemory.bytesAt initial source count⟩ template member outside
  exact ⟨kept,decodes mode template _ kept⟩

/-- Bind each completed header to the actual macro's reached MOVS prefix.
The source template is read in initial memory, before cursor saving. -/
theorem macro_header (mode : Mode) (p : StringMacroLayout.Params) (state : StringExecution.State mode)
    (ready : StringMacroLayout.Ready mode p state) (first rest : List Nat)
    (split : StringPlan.widths mode p.size=first++rest) (template : Template mode)
    (intact : Intact mode template state.principal.memory) (offset : Nat)
    (located : start mode template=p.source+offset) (complete : offset+header mode template≤first.sum) :
    Intact mode (relocate mode template (p.destination+offset))
      (StringMacroCopyPrefixes.reached mode p state first).principal.memory ∧
    Decodes mode (relocate mode template (p.destination+offset))
      (StringMacroCopyPrefixes.reached mode p state first).principal.memory := by
  rw [StringMacroCopyPrefixes.memory mode p state ready first rest split]
  have kept := copied_header mode template state.principal.memory
    (StringFields.prepared mode (StringMacroLayout.layout mode p) state.principal.memory state.sourceIndex state.destinationIndex)
    intact p.source p.destination first.sum offset located complete
  exact ⟨kept,decodes mode _ _ kept⟩

theorem macro_source (mode : Mode) (p : StringMacroLayout.Params) (state : StringExecution.State mode)
    (ready : StringMacroLayout.Ready mode p state) (first rest : List Nat)
    (split : StringPlan.widths mode p.size=first++rest) (template : Template mode)
    (intact : Intact mode template state.principal.memory) (offset : Nat)
    (located : start mode template=p.source+offset) (within : offset+header mode template≤p.size) :
    Intact mode template (StringMacroCopyPrefixes.reached mode p state first).principal.memory ∧
    Decodes mode template (StringMacroCopyPrefixes.reached mode p state first).principal.memory := by
  have kept : Intact mode template (StringMacroCopyPrefixes.reached mode p state first).principal.memory := by
    cases template with
    | pointer origin pc =>
      change pc=p.source+offset at located
      change PayloadTemplate.Prefix _ pc (Listing8PointerTemplate.fixed mode origin)
      rw [PayloadTemplate.Prefix,located,StringMacroCopyPrefixes.source_window_after mode p state ready first rest split]
      · rw [←located];exact intact
      · simpa only [Listing8PointerTemplate.fixed_length,header] using within
    | scalar pc d =>
      change pc=p.source+offset at located
      change PayloadTemplate.Prefix _ pc (Listing8ScalarTemplate.fixed d)
      rw [PayloadTemplate.Prefix,located,StringMacroCopyPrefixes.source_window_after mode p state ready first rest split]
      · rw [←located];exact intact
      · simpa only [Listing8ScalarTemplate.fixed_length,header] using within
  exact ⟨kept,decodes mode template _ kept⟩

end SmcTuring.Appendix.Listing8CopyTemplateWindows

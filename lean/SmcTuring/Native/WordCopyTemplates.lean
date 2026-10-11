module
public import SmcTuring.Native.FixedStackTemplates
public import SmcTuring.Native.WordCopyPacket

public section
namespace SmcTuring.Native.WordCopyTemplates

@[expose] def instructions (mode : Mode) (layout : ConversionLayout.Layout) :=
  (ConversionLayout.program mode layout).map (FixedStackTemplates.native mode)
@[expose] def entries (mode : Mode) (layout : ConversionLayout.Layout) :=
  FixedStackTemplates.place mode layout.start (instructions mode layout)

theorem encoding (mode : Mode) (layout : ConversionLayout.Layout) :
    FixedStackTemplates.bytes mode (instructions mode layout)=WordCopyPacket.bytes mode layout := by
  cases mode <;> rfl

theorem count (mode : Mode) (layout : ConversionLayout.Layout) : (entries mode layout).length=3 := by
  rw [entries,FixedStackTemplates.placed_count]
  rfl

theorem legal (mode : Mode) (layout : ConversionLayout.Layout) :
    ∀ entry∈entries mode layout,FixedStackTemplates.Legal mode entry.instruction := by
  apply FixedStackTemplates.placed_legal
  simp [instructions,ConversionLayout.program,FixedStackTemplates.native,FixedStackTemplates.Legal,StringForm.Legal]

theorem initial (mode : Mode) (layout : ConversionLayout.Layout) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory layout.start (WordCopyPacket.bytes mode layout).length=WordCopyPacket.bytes mode layout) :
    FixedStackTemplates.All mode (entries mode layout) memory :=
  FixedStackTemplates.placed_initial mode layout.start _ memory (by rw [encoding];exact current)

theorem bounds (mode : Mode) (layout : ConversionLayout.Layout) (entry : FixedStackTemplates.Entry mode)
    (member : entry∈entries mode layout) :
    layout.start≤entry.pc ∧ entry.pc+(FixedStackTemplates.encode mode entry.instruction).length≤ConversionLayout.endPC mode layout := by
  have h:=FixedStackTemplates.placed_bounds mode layout.start _ entry member
  rw [encoding,WordCopyPacket.bytes_length,←ConversionLayout.endpoint] at h
  exact h

end SmcTuring.Native.WordCopyTemplates

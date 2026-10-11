module
public import SmcTuring.Appendix.Listing8CopyTrace

public section
namespace SmcTuring.Appendix.Listing8CursorFields
open Native Listing8CopyImage

/-- DEFDATA's x86 label names its MOV entry; its x64 label already names
the final MOFFS operand. M10's DATAOFFS also applies to Listing 8 users. -/
@[expose] def label (mode : Mode) (entry : Nat) :=
  if mode = .x86 then entry else entry+StringCodec.fieldOffset mode
@[expose] def dataOffset (mode : Mode) := if mode = .x86 then 6 else 0
@[expose] def field (mode : Mode) (entry : Nat) := label mode entry+dataOffset mode

theorem field_is_operand (mode : Mode) (entry : Nat) : field mode entry = StringCodec.sourceField mode entry := by
  cases mode <;> rfl
theorem printed_x86_is_header (entry : Nat) : label .x86 entry < field .x86 entry := by
  simp [label,field,dataOffset]

theorem x86_bare_label_counterexample :
    let p : StringMacroLayout.Params := { start := 4096, source := 0, destination := 8192, size := 46 }
    let memory := ByteMemory.putBytes (fun _ => 0) p.start (StringMacroLayout.bytes .x86 p)
    MixedMemory.getWord .x86 memory (label .x86 p.start) ≠ Arithmetic.encodeNat .x86 p.source ∧
    MixedMemory.getWord .x86 memory (field .x86 p.start) = Arithmetic.encodeNat .x86 p.source := by
  decide

theorem x64_immediate_offset_counterexample :
    let p : StringMacroLayout.Params := { start := 4096, source := 0, destination := 8192, size := 64 }
    let memory := ByteMemory.putBytes (fun _ => 0) p.start (StringMacroLayout.bytes .x64 p)
    MixedMemory.getWord .x64 memory (label .x64 p.start+6) ≠ Arithmetic.encodeNat .x64 p.source ∧
    MixedMemory.getWord .x64 memory (field .x64 p.start) = Arithmetic.encodeNat .x64 p.source := by
  decide

/-- Corrected Listing 8 references read the actual initialized/restored
source cursor after both TRANSFERDATA calls, in either mode. -/
theorem source_cursor (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8CopyTrace.both mode l (initial mode l v backing seed)).principal.memory (field mode l.start) =
      Arithmetic.encodeNat mode l.sourceNode := by
  rw [field_is_operand]
  exact Listing8CopyTrace.cursor_retained mode l v r backing seed

end SmcTuring.Appendix.Listing8CursorFields

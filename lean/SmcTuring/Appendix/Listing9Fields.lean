module
public import SmcTuring.Appendix.Listing9MetadataPackets

public section
namespace SmcTuring.Appendix.Listing9Fields
open Native Listing9PackedLayout

/-- The printed DEFDATA32 label is the x86 header; the x64 MOFFSMOV label
is the full pointer payload. DATAOFFS converts both labels to operand fields. -/
@[expose] def printedLabel (mode : Mode) (owner : Nat) := if mode=.x86 then owner else StringInit.field mode owner
@[expose] def dataOffset (mode : Mode) := if mode=.x86 then 6 else 0

theorem operand_field (mode : Mode) (owner : Nat) : printedLabel mode owner+dataOffset mode=StringInit.field mode owner := by
  cases mode <;> rfl

theorem save_field (mode : Mode) (start transitions nodes : Nat) :
    printedLabel mode (saveOwner mode start transitions nodes)+dataOffset mode=(layout mode start transitions nodes).save :=
  operand_field mode _

theorem pointer_field (mode : Mode) (start transitions nodes : Nat) :
    printedLabel mode (pointerOwner mode start transitions nodes)+dataOffset mode=(layout mode start transitions nodes).pointer :=
  operand_field mode _

theorem x86_header_not_operand (owner : Nat) : printedLabel .x86 owner≠StringInit.field .x86 owner := by
  dsimp [printedLabel,StringInit.field,StringCodec.fieldOffset]
  omega

theorem corrected_pointer (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes) (backing : ByteMemory.Memory) :
    Execution.load mode (Listing9Image.memory mode start transitions nodes backing)
      (Arithmetic.encodeNat mode (printedLabel mode (pointerOwner mode start transitions nodes)+dataOffset mode))=
      Arithmetic.encodeNat mode (printedLabel mode (saveOwner mode start transitions nodes)+dataOffset mode) := by
  rw [pointer_field,save_field]
  exact (Listing9Image.initial_values mode start transitions nodes bounds backing).2

end SmcTuring.Appendix.Listing9Fields

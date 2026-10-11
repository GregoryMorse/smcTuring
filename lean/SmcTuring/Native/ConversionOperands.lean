module
public import SmcTuring.Native.ConversionImage

public section
namespace SmcTuring.Native.ConversionOperands
open Execution ConversionLayout ConversionEffects

/-- A word destination immediately after its owner's MOFFS prefix cannot
reach that prefix, even for the full eight-byte x64 address field. -/
theorem owner_prefix_outside (mode : Mode) (ownerPC : Nat) (index : Fin (moffsOperandOffset mode)) :
    ¬ByteMemory.Inside (ownerPC + moffsOperandOffset mode) mode.wordBytes (ownerPC + index.val) := by
  have small := index.isLt
  unfold ByteMemory.Inside
  omega

theorem destination_prefix (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) (ownerPC : Nat)
    (field : layout.destination = ownerPC + moffsOperandOffset mode) (intact : Protected.PrefixAt mode native.memory ownerPC) :
    Protected.PrefixAt mode (finish mode layout native).memory ownerPC := by
  rw [effect mode layout valid native entry, field, Protected.prefix_frame mode native.memory ownerPC _ _ (owner_prefix_outside mode ownerPC)]
  exact intact

/-- Import into an already initialized template yields an actually decodable
instruction containing the original source value, for both word widths. -/
theorem destination_fetch (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) (ownerPC : Nat)
    (field : layout.destination = ownerPC + moffsOperandOffset mode) (intact : Protected.PrefixAt mode native.memory ownerPC) :
    Fetch.fetch mode (finish mode layout native).memory ownerPC = some (.moffs (load mode native.memory (Arithmetic.encodeNat mode layout.source))) := by
  rw [Protected.fetch_moffs mode _ ownerPC (destination_prefix mode layout valid native entry ownerPC field intact),
    effect mode layout valid native entry, ←field, Protected.word_at_put]

theorem source_prefix (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) (ownerPC : Nat)
    (intact : Protected.PrefixAt mode native.memory ownerPC)
    (separate : forall index : Fin (moffsOperandOffset mode), ¬ByteMemory.Inside layout.destination mode.wordBytes (ownerPC + index.val)) :
    Protected.PrefixAt mode (finish mode layout native).memory ownerPC := by
  rw [effect mode layout valid native entry, Protected.prefix_frame mode native.memory ownerPC _ _ separate]
  exact intact

/-- A source owner remains decodable with the same live word after export. -/
theorem source_fetch (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) (ownerPC : Nat)
    (field : layout.source = ownerPC + moffsOperandOffset mode) (intact : Protected.PrefixAt mode native.memory ownerPC)
    (separate : forall index : Fin (moffsOperandOffset mode), ¬ByteMemory.Inside layout.destination mode.wordBytes (ownerPC + index.val)) :
    Fetch.fetch mode (finish mode layout native).memory ownerPC = some (.moffs (load mode native.memory (Arithmetic.encodeNat mode layout.source))) := by
  rw [Protected.fetch_moffs mode _ ownerPC (source_prefix mode layout valid native entry ownerPC intact separate), ←field]
  have positive : 0 < mode.wordBytes := by cases mode <;> decide
  have bound := valid.sourceFits
  have fits : layout.source < 2 ^ (8 * mode.wordBytes) := by omega
  rw [←Protected.encoded_address_load mode _ layout.source fits, source_value mode layout valid native entry]

end SmcTuring.Native.ConversionOperands

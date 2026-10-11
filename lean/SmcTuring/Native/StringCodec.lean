module
public import SmcTuring.Native.StringFields
public import SmcTuring.Native.Relocation
public import SmcTuring.Appendix.ByteCode

public section
namespace SmcTuring.Native.StringCodec
open LittleEndian
@[expose] def initialSize (mode : Mode) : Nat := match mode with | .x86 => 10 | .x64 => 27
@[expose] def fieldOffset (mode : Mode) : Nat := match mode with | .x86 => 6 | .x64 => 19
@[expose] def exchangeSize (mode : Mode) : Nat := match mode with | .x86 => 6 | .x64 => 7
@[expose] def subSize (mode : Mode) (size : Nat) : Nat := exchangeSize mode + (if size < 128 then 1 else 4)
@[expose] def sourceField (mode : Mode) (start : Nat) : Nat := start + fieldOffset mode
@[expose] def destinationStart (mode : Mode) (start : Nat) : Nat := start + initialSize mode + exchangeSize mode
@[expose] def destinationField (mode : Mode) (start : Nat) : Nat := destinationStart mode start + fieldOffset mode
@[expose] def bodyStart (mode : Mode) (start : Nat) : Nat := start + 2 * (initialSize mode + exchangeSize mode)
@[expose] def bodyEnd (mode : Mode) (start size : Nat) : Nat := bodyStart mode start + (StringPlan.bytes mode size).length
@[expose] def endpoint (mode : Mode) (start size : Nat) : Nat := bodyEnd mode start size + 2 * (exchangeSize mode + subSize mode size)

@[expose] def initialBytes (mode : Mode) (start field initial : Nat) : List Byte :=
  match mode with
  | .x86 => Appendix.ByteCode.encode (.immediate .store (BitVec.ofNat 32 field) (BitVec.ofNat 32 initial))
  | .x64 =>
      encode .x64 (.memory .exchangeAcc (Relocation.instructionDisp .x64 .exchangeAcc start field)) ++
      encode .x64 (.memory .storeAcc (Relocation.instructionDisp .x64 .storeAcc (start+7) field)) ++
      encode .x64 .exchangeIndirect ++ encode .x64 (.moffs (Arithmetic.encodeNat .x64 initial))

/-- SI/DI exchange: the same complete absolute/RIP field syntax as the selected
native codec, with the actual ModRM register number (6/7). -/
@[expose] def exchangeBytes (mode : Mode) (destination : Bool) (pc field : Nat) : List Byte :=
  wordPrefix mode ++ [0x87, if destination then 0x3D else 0x35] ++
    wordEncode 4 (Relocation.memoryDisp mode (pc+exchangeSize mode) field)
@[expose] def subBytes (mode : Mode) (pc field size : Nat) : List Byte :=
  wordPrefix mode ++ [if size < 128 then 0x83 else 0x81, 0x2D] ++
    wordEncode 4 (Relocation.memoryDisp mode (pc+subSize mode size) field) ++
    (if size < 128 then [BitVec.ofNat 8 size] else LittleEndian.encode 4 size)

@[expose] def bytes (mode : Mode) (start source destination size : Nat) : List Byte :=
  let sf := sourceField mode start
  let ds := destinationStart mode start
  let df := destinationField mode start
  let tail := bodyEnd mode start size
  let exchange := exchangeSize mode
  let subtract := subSize mode size
  initialBytes mode start sf source ++ exchangeBytes mode false (start+initialSize mode) sf ++
  initialBytes mode ds df destination ++ exchangeBytes mode true (ds+initialSize mode) df ++
  StringPlan.bytes mode size ++ exchangeBytes mode false tail sf ++ subBytes mode (tail+exchange) sf size ++
  exchangeBytes mode true (tail+exchange+subtract) df ++ subBytes mode (tail+2*exchange+subtract) df size

theorem initial_length (mode : Mode) (start field initial : Nat) : (initialBytes mode start field initial).length = initialSize mode := by cases mode <;> rfl

theorem exchange_length (mode : Mode) (destination : Bool) (pc field : Nat) : (exchangeBytes mode destination pc field).length = exchangeSize mode := by cases mode <;> cases destination <;> rfl

theorem sub_length (mode : Mode) (pc field size : Nat) : (subBytes mode pc field size).length = subSize mode size := by
  unfold subBytes subSize
  split <;> cases mode <;> simp_all [exchangeSize, wordPrefix]

theorem field_end (mode : Mode) (start : Nat) : sourceField mode start + mode.wordBytes = start + initialSize mode := by cases mode <;> simp [sourceField,fieldOffset,initialSize,Mode.wordBytes]

theorem destination_field_end (mode : Mode) (start : Nat) : destinationField mode start + mode.wordBytes = destinationStart mode start + initialSize mode := by
  exact field_end mode (destinationStart mode start)

theorem body_coordinate (mode : Mode) (start : Nat) : destinationStart mode start + initialSize mode + exchangeSize mode = bodyStart mode start := by
  unfold destinationStart bodyStart
  omega

/-- Complete initializer/cursor/MOVS packet length, including imm8/imm32 SUB
selection. This is a codec/geometry certificate; instruction effects remain
the independently checked copy, cursor and unified-byte contracts. -/
theorem whole_length (mode : Mode) (start source destination size : Nat) :
    (bytes mode start source destination size).length = endpoint mode start size - start := by
  simp only [bytes, List.length_append, initial_length, exchange_length, sub_length]
  unfold endpoint bodyEnd bodyStart
  omega

end SmcTuring.Native.StringCodec

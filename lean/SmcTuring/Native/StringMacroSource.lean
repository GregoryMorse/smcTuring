module
public import SmcTuring.Native.StringMacroTrace
public import SmcTuring.Native.MixedMemory
public import SmcTuring.Native.ByteWindow

public section
namespace SmcTuring.Native.StringMacroSource
open StringMacroLayout

/-- All macro bytes following its source operand. Their encoding depends
only on placement, destination and count, so changing the source word keeps
this complete suffix unchanged. -/
@[expose] def tailBytes (mode : Mode) (p : Params) :=
  let sf:=StringCodec.sourceField mode p.start
  let ds:=StringCodec.destinationStart mode p.start
  let df:=StringCodec.destinationField mode p.start
  let tail:=StringCodec.bodyEnd mode p.start p.size
  let exchange:=StringCodec.exchangeSize mode
  let subtract:=StringCodec.subSize mode p.size
  StringCodec.exchangeBytes mode false (p.start+StringCodec.initialSize mode) sf ++
  StringCodec.initialBytes mode ds df p.destination ++
  StringCodec.exchangeBytes mode true (ds+StringCodec.initialSize mode) df ++
  StringPlan.bytes mode p.size ++ StringCodec.exchangeBytes mode false tail sf ++
  StringCodec.subBytes mode (tail+exchange) sf p.size ++
  StringCodec.exchangeBytes mode true (tail+exchange+subtract) df ++
  StringCodec.subBytes mode (tail+2*exchange+subtract) df p.size

theorem shape (mode : Mode) (p : Params) :
    bytes mode p=StringInit.leading mode p.start++
      LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode p.source)++tailBytes mode p := by
  simp only [bytes,StringCodec.bytes,tailBytes]
  rw [show StringCodec.initialBytes mode p.start (StringCodec.sourceField mode p.start) p.source=
    StringInit.bytes mode p.start p.source from rfl,StringInit.initial_shape]
  simp only [List.append_assoc]
theorem tail_length (mode : Mode) (p : Params) :
    p.start+StringCodec.initialSize mode+(tailBytes mode p).length=endpoint mode p := by
  have extent:=StringCodec.whole_length mode p.start p.source p.destination p.size
  change (bytes mode p).length=endpoint mode p-p.start at extent
  rw [shape] at extent
  simp only [List.length_append,StringInit.leading_length,LittleEndian.word_encode_length] at extent
  have field:=StringCodec.field_end mode p.start
  have lower : p.start≤endpoint mode p := by
    dsimp [endpoint,StringCodec.endpoint,StringCodec.bodyEnd,StringCodec.bodyStart];omega
  dsimp only [StringCodec.sourceField] at field
  omega
theorem windows (mode : Mode) (p : Params) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory p.start (bytes mode p).length=bytes mode p) :
    ByteMemory.bytesAt memory p.start (StringCodec.fieldOffset mode)=StringInit.leading mode p.start ∧
    ByteMemory.bytesAt memory (p.start+StringCodec.initialSize mode) (tailBytes mode p).length=tailBytes mode p := by
  rw [shape] at current
  have first:=ByteWindow.packet memory p.start [] (StringInit.leading mode p.start)
    (LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode p.source)++tailBytes mode p)
    (by simpa only [List.nil_append,List.append_assoc] using current)
  have last:=ByteWindow.packet memory p.start
    (StringInit.leading mode p.start++LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode p.source)) (tailBytes mode p) []
    (by simpa only [List.append_nil] using current)
  have coordinate:=StringCodec.field_end mode p.start
  dsimp only [StringCodec.sourceField] at coordinate
  rw [List.length_append,StringInit.leading_length,LittleEndian.word_encode_length,←Nat.add_assoc,coordinate] at last
  exact ⟨by simpa only [List.length_nil,Nat.add_zero,StringInit.leading_length] using first,last⟩
theorem word_bytes (mode : Mode) (memory : ByteMemory.Memory) (field source : Nat)
    (value : MixedMemory.getWord mode memory field=Arithmetic.encodeNat mode source) :
    ByteMemory.bytesAt memory field mode.wordBytes=LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode source) := by
  apply Eq.symm
  exact LittleEndian.word_encode_decode mode.wordBytes _ _ (by
    change ByteMemory.readWord mode memory field=some (Arithmetic.encodeNat mode source)
    rw [MixedMemory.read_total,value])
/-- Reconstruct the current macro from its framed header/suffix and actual
decoded source operand. No initialized replacement memory is constructed. -/
theorem current (mode : Mode) (p : Params) (memory : ByteMemory.Memory)
    (header : ByteMemory.bytesAt memory p.start (StringCodec.fieldOffset mode)=StringInit.leading mode p.start)
    (tail : ByteMemory.bytesAt memory (p.start+StringCodec.initialSize mode) (tailBytes mode p).length=tailBytes mode p)
    (source : MixedMemory.getWord mode memory (StringCodec.sourceField mode p.start)=Arithmetic.encodeNat mode p.source) :
    ByteMemory.bytesAt memory p.start (bytes mode p).length=bytes mode p := by
  rw [shape]
  have first:=ByteWindow.join memory p.start (StringInit.leading mode p.start)
    (LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode p.source))
    (by simpa only [StringInit.leading_length] using header)
    (by simpa only [StringInit.leading_length,StringCodec.sourceField,LittleEndian.word_encode_length] using word_bytes mode memory _ _ source)
  have coordinate:=StringCodec.field_end mode p.start
  dsimp only [StringCodec.sourceField] at coordinate
  exact ByteWindow.join memory p.start _ _ first (by
    simpa only [List.length_append,StringInit.leading_length,LittleEndian.word_encode_length,←Nat.add_assoc,coordinate] using tail)

end SmcTuring.Native.StringMacroSource

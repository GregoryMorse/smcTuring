module
public import SmcTuring.Native.StringProgram

public section
namespace SmcTuring.Native.StringMacroLayout
open StringExecution ByteMemory

structure Params where
  start : Nat
  source : Nat
  destination : Nat
  size : Nat

@[expose] def bodyStart (mode : Mode) (p : Params) : Nat := StringCodec.bodyStart mode p.start
@[expose] def sourceTail (mode : Mode) (p : Params) : Nat := StringCodec.bodyEnd mode p.start p.size
@[expose] def destinationTail (mode : Mode) (p : Params) : Nat := StringRestore.endpoint mode (sourceTail mode p) p.size
@[expose] def endpoint (mode : Mode) (p : Params) : Nat := StringCodec.endpoint mode p.start p.size
@[expose] def prefixBytes (mode : Mode) (p : Params) : List LittleEndian.Byte := StringSetupTrace.bytes mode p.start p.source p.destination
@[expose] def body (mode : Mode) (p : Params) : List LittleEndian.Byte := StringPlan.bytes mode p.size
@[expose] def sourceBytes (mode : Mode) (p : Params) : List LittleEndian.Byte :=
  StringRestore.bytes mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size
@[expose] def destinationBytes (mode : Mode) (p : Params) : List LittleEndian.Byte :=
  StringRestore.bytes mode true (destinationTail mode p) (StringCodec.destinationField mode p.start) p.size
@[expose] def bytes (mode : Mode) (p : Params) : List LittleEndian.Byte := StringCodec.bytes mode p.start p.source p.destination p.size
@[expose] def layout (mode : Mode) (p : Params) : StringFields.Layout :=
  ⟨p.source,p.destination,p.size,StringCodec.sourceField mode p.start,StringCodec.destinationField mode p.start⟩
@[expose] def Outside (mode : Mode) (p : Params) (buffer : Nat) : Prop :=
  buffer+max p.size mode.wordBytes ≤ p.start ∨ endpoint mode p ≤ buffer

/-- Original image and static resources only. Pointed-word bounds cover the
initializer even when the requested MOVS count is shorter than one word. -/
structure Ready (mode : Mode) (p : Params) (state : State mode) : Prop where
  entry : state.principal.pc = Arithmetic.encodeNat mode p.start
  forward : state.backwards = false
  sizeFits : p.size < 2^31
  codeFits : endpoint mode p < 2^(8*mode.wordBytes)
  sourceFits : p.source+max p.size mode.wordBytes < 2^(8*mode.wordBytes)
  destinationFits : p.destination+max p.size mode.wordBytes < 2^(8*mode.wordBytes)
  buffers : StringCopy.Apart p.source p.destination p.size
  sourceOutside : Outside mode p p.source
  destinationOutside : Outside mode p p.destination
  initialized : bytesAt state.principal.memory p.start (bytes mode p).length = bytes mode p

theorem split_bytes (mode : Mode) (p : Params) (fits : p.size < 2^31) :
    bytes mode p = prefixBytes mode p++body mode p++sourceBytes mode p++destinationBytes mode p := by
  rw [bytes,←StringProgram.encoding mode p.start p.source p.destination p.size fits]
  simp only [StringProgram.forms,List.map_append,List.flatten_append,StringSetupTrace.forms_encoding,StringProgram.body_encoding,
    StringRestore.forms_encoding mode _ _ _ _ fits]
  rfl

theorem coordinates (mode : Mode) (p : Params) :
    p.start+(prefixBytes mode p).length = bodyStart mode p ∧
    bodyStart mode p+(body mode p).length = sourceTail mode p ∧
    sourceTail mode p+(sourceBytes mode p).length = destinationTail mode p ∧
    destinationTail mode p+(destinationBytes mode p).length = endpoint mode p := by
  have prefixLength := StringProgram.prefix_extent mode p.start p.source p.destination
  have sourceLength : (sourceBytes mode p).length = StringCodec.exchangeSize mode+StringCodec.subSize mode p.size := by
    simp only [sourceBytes,StringRestore.bytes,List.length_append,StringCodec.exchange_length,StringCodec.sub_length]
  have destinationLength : (destinationBytes mode p).length = StringCodec.exchangeSize mode+StringCodec.subSize mode p.size := by
    simp only [destinationBytes,StringRestore.bytes,List.length_append,StringCodec.exchange_length,StringCodec.sub_length]
  change (prefixBytes mode p).length = StringCodec.bodyStart mode p.start-p.start at prefixLength
  simp only [bodyStart,sourceTail,destinationTail,endpoint,body,prefixLength,sourceLength,destinationLength,
    StringRestore.endpoint,StringCodec.endpoint,StringCodec.bodyEnd,StringCodec.bodyStart]
  constructor
  · omega
  · exact ⟨True.intro,by omega,by omega⟩

theorem field_coordinates (mode : Mode) (p : Params) :
    p.start ≤ StringCodec.sourceField mode p.start ∧
    StringCodec.sourceField mode p.start+mode.wordBytes ≤ StringCodec.destinationField mode p.start ∧
    StringCodec.destinationField mode p.start+mode.wordBytes ≤ bodyStart mode p ∧
    bodyStart mode p ≤ sourceTail mode p ∧ sourceTail mode p ≤ destinationTail mode p ∧
    destinationTail mode p ≤ endpoint mode p := by
  have sourceEnd := StringCodec.field_end mode p.start
  have destinationEnd := StringCodec.destination_field_end mode p.start
  have bodyPC := StringCodec.body_coordinate mode p.start
  simp only [StringCodec.sourceField,StringCodec.destinationField,StringCodec.destinationStart] at sourceEnd destinationEnd bodyPC ⊢
  simp only [bodyStart,sourceTail,destinationTail,endpoint,StringCodec.bodyEnd,StringCodec.endpoint,StringRestore.endpoint]
  constructor
  · omega
  · constructor
    · omega
    · constructor
      · omega
      · exact ⟨by omega,by omega,by omega⟩

theorem repeat_length (count : Nat) (packet : List LittleEndian.Byte) :
    (List.replicate count packet).flatten.length = count*packet.length := by
  induction count with
  | zero => simp
  | succ count ih => simp only [List.replicate_succ,List.flatten_cons,List.length_append,ih,Nat.succ_mul]; omega

theorem body_bound (mode : Mode) (size : Nat) : (StringPlan.bytes mode size).length ≤ size/4+4 := by
  cases mode <;> simp only [StringPlan.bytes,StringPlan.widths,List.map_append,List.map_replicate,List.flatten_append,List.length_append,repeat_length]
  · change size/4*1+((size%4)/2)*2+(size%2)*1 ≤ size/4+4
    omega
  · change size/8*2+((size%8)/4)*1+((size%4)/2)*2+(size%2)*1 ≤ size/4+4
    omega

/-- Both literal emitters fit rel32's signed reach under the stated immediate
bound. Backward cursor references are derived, not assumed as address hits. -/
theorem span_bound (mode : Mode) (p : Params) (fits : p.size < 2^31) : (bytes mode p).length < 2^31 := by
  have bodySmall := body_bound mode p.size
  simp only [bytes,StringCodec.bytes,List.length_append,StringCodec.initial_length,StringCodec.exchange_length,StringCodec.sub_length]
  cases mode <;> simp only [StringCodec.initialSize,StringCodec.exchangeSize,StringCodec.subSize] at * <;>
    split <;> omega

theorem internal_range (mode : Mode) (p : Params) (fits : p.size < 2^31) (next field : Nat)
    (nextWithin : p.start ≤ next ∧ next ≤ endpoint mode p)
    (fieldWithin : p.start ≤ field ∧ field ≤ endpoint mode p) : Relocation.SignedDelta next field := by
  have width := span_bound mode p fits
  rw [bytes,StringCodec.whole_length] at width
  change endpoint mode p-p.start < 2^31 at width
  unfold Relocation.SignedDelta Relocation.delta
  constructor <;> omega

theorem tail_ranges (mode : Mode) (p : Params) (fits : p.size < 2^31) :
    Relocation.SignedDelta (sourceTail mode p+StringCodec.exchangeSize mode) (StringCodec.sourceField mode p.start) ∧
    Relocation.SignedDelta (destinationTail mode p) (StringCodec.sourceField mode p.start) ∧
    Relocation.SignedDelta (destinationTail mode p+StringCodec.exchangeSize mode) (StringCodec.destinationField mode p.start) ∧
    Relocation.SignedDelta (endpoint mode p) (StringCodec.destinationField mode p.start) := by
  have positions := field_coordinates mode p
  have a := StringCodec.field_end mode p.start
  have b := StringCodec.destination_field_end mode p.start
  have first : p.start ≤ sourceTail mode p+StringCodec.exchangeSize mode ∧ sourceTail mode p+StringCodec.exchangeSize mode ≤ endpoint mode p := by
    simp only [sourceTail,endpoint,StringCodec.endpoint,StringCodec.bodyEnd,StringCodec.bodyStart]
    constructor <;> omega
  have second : p.start ≤ destinationTail mode p ∧ destinationTail mode p ≤ endpoint mode p := by omega
  have third : p.start ≤ destinationTail mode p+StringCodec.exchangeSize mode ∧ destinationTail mode p+StringCodec.exchangeSize mode ≤ endpoint mode p := by
    simp only [sourceTail,destinationTail,endpoint,StringRestore.endpoint,StringCodec.endpoint,StringCodec.bodyEnd,StringCodec.bodyStart]
    constructor <;> omega
  have sourceWithin : p.start ≤ StringCodec.sourceField mode p.start ∧ StringCodec.sourceField mode p.start ≤ endpoint mode p := by omega
  have destinationWithin : p.start ≤ StringCodec.destinationField mode p.start ∧ StringCodec.destinationField mode p.start ≤ endpoint mode p := by omega
  exact ⟨internal_range mode p fits _ _ first sourceWithin,internal_range mode p fits _ _ second sourceWithin,
    internal_range mode p fits _ _ third destinationWithin,internal_range mode p fits _ _ ⟨by omega,(Nat.le_refl _)⟩ destinationWithin⟩

theorem source_capacity (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    p.source+p.size < 2^(8*mode.wordBytes) ∧ p.source+mode.wordBytes < 2^(8*mode.wordBytes) ∧ p.source < 2^(8*mode.wordBytes) := by
  have capacity := ready.sourceFits
  exact ⟨by omega,by omega,by omega⟩

theorem destination_capacity (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    p.destination+p.size < 2^(8*mode.wordBytes) ∧ p.destination+mode.wordBytes < 2^(8*mode.wordBytes) ∧ p.destination < 2^(8*mode.wordBytes) := by
  have capacity := ready.destinationFits
  exact ⟨by omega,by omega,by omega⟩

theorem prefix_capacity (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    bodyStart mode p < 2^(8*mode.wordBytes) := by
  have positions := field_coordinates mode p
  have capacity := ready.codeFits
  omega

theorem fields_separate (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) : StringFields.Separate mode (layout mode p) := by
  have positions := field_coordinates mode p
  have source := ready.sourceOutside
  have destination := ready.destinationOutside
  unfold Outside at source destination
  refine ⟨ready.buffers,Or.inl positions.2.1,?_,?_,?_,?_⟩ <;> intro index <;> have small := index.isLt <;> (try simp only [layout] at small) <;>
    simp only [layout,Inside]
  · rcases source with before | after <;> omega
  · rcases source with before | after <;> omega
  · rcases destination with before | after <;> omega
  · rcases destination with before | after <;> omega

theorem source_cursor_frame (mode : Mode) (p : Params) (observed count : Nat) (memory : Memory) (value : Word mode)
    (afterBody : bodyStart mode p ≤ observed) :
    bytesAt (putWord mode memory (StringCodec.sourceField mode p.start) value) observed count = bytesAt memory observed count := by
  unfold putWord
  apply bytes_at_frame
  intro index
  have positions := field_coordinates mode p
  simp only [LittleEndian.word_encode_length,Inside]
  omega

theorem destination_cursor_frame (mode : Mode) (p : Params) (observed count : Nat) (memory : Memory) (value : Word mode)
    (afterBody : bodyStart mode p ≤ observed) :
    bytesAt (putWord mode memory (StringCodec.destinationField mode p.start) value) observed count = bytesAt memory observed count := by
  unfold putWord
  apply bytes_at_frame
  intro index
  have positions := field_coordinates mode p
  simp only [LittleEndian.word_encode_length,Inside]
  omega

theorem copy_code_frame (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) (memory : Memory)
    (observed count : Nat) (window : p.start ≤ observed ∧ observed+count ≤ endpoint mode p) :
    bytesAt (putBytes memory p.destination (bytesAt memory p.source p.size)) observed count = bytesAt memory observed count := by
  apply bytes_at_frame
  intro index
  have outside := ready.destinationOutside
  have small := index.isLt
  unfold Outside at outside
  simp only [bytes_at_length,Inside]
  rcases outside with before | after <;> omega

end SmcTuring.Native.StringMacroLayout

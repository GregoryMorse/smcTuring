module
public import SmcTuring.Appendix.Listing8LiveCopies
public import SmcTuring.Native.StringMacroSource

public section
namespace SmcTuring.Appendix.Listing8MainCopyImage
open Native Listing8CopyImage Listing8Prototypes

/-- Present immutable macro fragments and its actual full-width source operand.
No future state, readiness, image or trace is a field. -/
structure MacroCurrent (mode : Mode) (p : StringMacroLayout.Params) (memory : ByteMemory.Memory) : Prop where
  header : ByteMemory.bytesAt memory p.start (StringCodec.fieldOffset mode)=StringInit.leading mode p.start
  tail : ByteMemory.bytesAt memory (p.start+StringCodec.initialSize mode)
    (StringMacroSource.tailBytes mode p).length=StringMacroSource.tailBytes mode p
  source : MixedMemory.getWord mode memory (StringCodec.sourceField mode p.start)=Arithmetic.encodeNat mode p.source

/-- The current two copy macros, four retarget instructions and two logical
source declarations, all in the same present main-entry memory. -/
structure Current (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory) : Prop where
  nodeMacro : MacroCurrent mode (nodeParams mode l) memory
  ruleMacro : MacroCurrent mode (transitionParams mode l) memory
  patches : ByteMemory.bytesAt memory (patchStart mode l) (patchBytes mode l).length=patchBytes mode l
  node : ByteMemory.bytesAt memory l.sourceNode (nodeSpan mode)=sourceNodeBytes mode l v
  rule : ByteMemory.bytesAt memory l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l v

theorem macro_current (mode : Mode) (p : StringMacroLayout.Params) (memory : ByteMemory.Memory)
    (current : MacroCurrent mode p memory) :
    ByteMemory.bytesAt memory p.start (StringMacroLayout.bytes mode p).length=StringMacroLayout.bytes mode p :=
  StringMacroSource.current mode p memory current.header current.tail current.source

theorem macro_source (mode : Mode) (p : StringMacroLayout.Params) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory p.start (StringMacroLayout.bytes mode p).length=StringMacroLayout.bytes mode p) :
    MixedMemory.getWord mode memory (StringCodec.sourceField mode p.start)=Arithmetic.encodeNat mode p.source := by
  rw [StringMacroSource.shape] at current
  have packet:=ByteWindow.packet memory p.start (StringInit.leading mode p.start)
    (LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode p.source)) (StringMacroSource.tailBytes mode p) current
  simp only [StringInit.leading_length,LittleEndian.word_encode_length] at packet
  change ByteMemory.bytesAt memory (StringCodec.sourceField mode p.start) mode.wordBytes=_ at packet
  have decoded : ByteMemory.readWord mode memory (StringCodec.sourceField mode p.start)=some (Arithmetic.encodeNat mode p.source) := by
    change LittleEndian.wordDecode mode.wordBytes (ByteMemory.bytesAt memory (StringCodec.sourceField mode p.start) mode.wordBytes)=_
    rw [packet,LittleEndian.word_decode_encode]
  rw [MixedMemory.read_total] at decoded
  exact Option.some.inj decoded

theorem macro_from_packet (mode : Mode) (p : StringMacroLayout.Params) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory p.start (StringMacroLayout.bytes mode p).length=StringMacroLayout.bytes mode p) :
    MacroCurrent mode p memory :=
  ⟨(StringMacroSource.windows mode p memory current).1,(StringMacroSource.windows mode p memory current).2,
    macro_source mode p memory current⟩

theorem from_packets (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory)
    (nodeMacro : ByteMemory.bytesAt memory l.start (StringMacroLayout.bytes mode (nodeParams mode l)).length=StringMacroLayout.bytes mode (nodeParams mode l))
    (ruleMacro : ByteMemory.bytesAt memory (secondStart mode l) (StringMacroLayout.bytes mode (transitionParams mode l)).length=StringMacroLayout.bytes mode (transitionParams mode l))
    (patches : ByteMemory.bytesAt memory (patchStart mode l) (patchBytes mode l).length=patchBytes mode l)
    (node : ByteMemory.bytesAt memory l.sourceNode (nodeSpan mode)=sourceNodeBytes mode l v)
    (rule : ByteMemory.bytesAt memory l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l v) :
    Current mode l v memory :=
  ⟨macro_from_packet mode _ memory nodeMacro,macro_from_packet mode _ memory ruleMacro,patches,node,rule⟩

theorem node_current (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory)
    (current : Current mode l v memory) :
    ByteMemory.bytesAt memory l.start (StringMacroLayout.bytes mode (nodeParams mode l)).length=StringMacroLayout.bytes mode (nodeParams mode l) :=
  macro_current mode _ memory current.nodeMacro

theorem rule_current (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory)
    (current : Current mode l v memory) :
    ByteMemory.bytesAt memory (secondStart mode l) (StringMacroLayout.bytes mode (transitionParams mode l)).length=StringMacroLayout.bytes mode (transitionParams mode l) :=
  macro_current mode _ memory current.ruleMacro

end SmcTuring.Appendix.Listing8MainCopyImage

module
public import SmcTuring.Native.StringDwordCopy
public import SmcTuring.Native.StackWindows

public section
namespace SmcTuring.Native.WordCopyPacket
@[expose] def bytes (mode : Mode) (l : ConversionLayout.Layout) := (ConversionLayout.program mode l).flatMap (Native.encode mode)
theorem bytes_length (mode : Mode) (l : ConversionLayout.Layout) : (bytes mode l).length=ConversionLayout.span mode := by cases mode <;> rfl
theorem intact (mode : Mode) (l : ConversionLayout.Layout) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory l.start (bytes mode l).length=bytes mode l) :
    ControlImage.Intact mode (ConversionLayout.entries mode l) memory := by
  let a:=Native.encode mode (ConversionLayout.first mode l)
  let b:=Native.encode mode (ConversionLayout.second mode l)
  let c:=Native.encode mode (ConversionLayout.third mode l)
  have code : ByteMemory.bytesAt memory l.start (a++b++c).length=a++b++c := by
    simpa only [bytes,ConversionLayout.program,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using current
  have first:=ByteWindow.packet memory l.start [] a (b++c) (by simpa only [List.nil_append,List.append_assoc] using code)
  have second:=ByteWindow.packet memory l.start a b c code
  have third:=ByteWindow.packet memory l.start (a++b) c [] (by simpa only [List.append_nil] using code)
  intro entry member
  change entry ∈ ConversionLayout.entries mode l at member
  simp only [ConversionLayout.entries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa only [ControlImage.PacketIntact,List.length_nil,Nat.add_zero] using first
  · have length : a.length=ConversionLayout.exchangeSize mode := by cases mode <;> rfl
    simpa only [ControlImage.PacketIntact,length,ConversionLayout.secondPC] using second
  · have length : (a++b).length=ConversionLayout.exchangeSize mode+ConversionLayout.storeSize mode := by cases mode <;> rfl
    simpa only [ControlImage.PacketIntact,length,ConversionLayout.thirdPC,ConversionLayout.secondPC,Nat.add_assoc] using third

theorem trace (mode : Mode) (l : ConversionLayout.Layout) (valid : ConversionLayout.Admissible mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (current : ByteMemory.bytesAt state.principal.memory l.start (bytes mode l).length=bytes mode l) :
    StringDword.Trace mode state (StringDwordCopy.wordProgram mode l) (StringDwordCopy.wordFinish mode l state) :=
  StringDwordCopy.word_trace mode l valid state entry (intact mode l _ current)
theorem effect (mode : Mode) (l : ConversionLayout.Layout) (valid : ConversionLayout.Admissible mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start) :
    StringDwordCopy.wordFinish mode l state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (ConversionLayout.endPC mode l)
      memory:=ByteMemory.putWord mode state.principal.memory l.destination (MixedMemory.getWord mode state.principal.memory l.source)}} := by
  have positive : 0<mode.wordBytes := by cases mode <;> decide
  have fits : l.source<2^(8*mode.wordBytes) := by have h:=valid.sourceFits;omega
  rw [StringDwordCopy.wordFinish,ConversionEffects.effect mode l valid state.principal entry,MixedMemory.load_nat mode _ _ fits]
end SmcTuring.Native.WordCopyPacket

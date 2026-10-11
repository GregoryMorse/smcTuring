module
public import SmcTuring.Appendix.Listing8ResetLayout

public section
namespace SmcTuring.Appendix.Listing8ResetPackets
open Native Listing8ResetLayout
@[expose] def Initial (mode : Mode) (l : Layout) (memory : ByteMemory.Memory) :=
  ByteMemory.bytesAt memory l.start (bytes mode l).length=bytes mode l

theorem store_current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory)
    (initial : Initial mode l memory) :
    ByteMemory.bytesAt memory l.start 10=DwordArithmetic.encode (store mode l) := by
  have packet:=ByteWindow.packet memory l.start [] (DwordArithmetic.encode (store mode l))
    (WordCopyPacket.bytes mode (inputCopy mode l)++StringInit.bytes mode (ownerPC mode l) l.ttape++
      WordCopyPacket.bytes mode (transitionCopy mode l)++TerminalMarker.bytes mode (markerPC mode l))
    (by simpa only [Initial,bytes,List.nil_append,List.append_assoc] using initial)
  simpa only [List.length_nil,Nat.add_zero,DwordArithmetic.encode_length,store,DwordArithmetic.length] using packet

theorem input_current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory)
    (initial : Initial mode l memory) :
    ByteMemory.bytesAt memory (inputCopy mode l).start (WordCopyPacket.bytes mode (inputCopy mode l)).length=
      WordCopyPacket.bytes mode (inputCopy mode l) := by
  have packet:=ByteWindow.packet memory l.start (DwordArithmetic.encode (store mode l))
    (WordCopyPacket.bytes mode (inputCopy mode l))
    (StringInit.bytes mode (ownerPC mode l) l.ttape++WordCopyPacket.bytes mode (transitionCopy mode l)++
      TerminalMarker.bytes mode (markerPC mode l))
    (by simpa only [Initial,bytes,List.append_assoc] using initial)
  simpa only [DwordArithmetic.encode_length,store,DwordArithmetic.length,inputCopy] using packet

theorem owner_current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory)
    (initial : Initial mode l memory) :
    ByteMemory.bytesAt memory (ownerPC mode l) (StringCodec.initialSize mode)=StringInit.bytes mode (ownerPC mode l) l.ttape := by
  have packet:=ByteWindow.packet memory l.start
    (DwordArithmetic.encode (store mode l)++WordCopyPacket.bytes mode (inputCopy mode l))
    (StringInit.bytes mode (ownerPC mode l) l.ttape)
    (WordCopyPacket.bytes mode (transitionCopy mode l)++TerminalMarker.bytes mode (markerPC mode l))
    (by simpa only [Initial,bytes,List.append_assoc] using initial)
  have location : l.start+(DwordArithmetic.encode (store mode l)++WordCopyPacket.bytes mode (inputCopy mode l)).length=ownerPC mode l := by
    rw [List.length_append,DwordArithmetic.encode_length,WordCopyPacket.bytes_length]
    simp only [store,DwordArithmetic.length,ownerPC,ConversionLayout.endpoint,inputCopy,Nat.add_assoc]
  rw [location] at packet
  simpa only [StringInit.bytes,StringCodec.initial_length] using packet

theorem transition_current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory)
    (initial : Initial mode l memory) :
    ByteMemory.bytesAt memory (transitionCopy mode l).start (WordCopyPacket.bytes mode (transitionCopy mode l)).length=
      WordCopyPacket.bytes mode (transitionCopy mode l) := by
  have packet:=ByteWindow.packet memory l.start
    (DwordArithmetic.encode (store mode l)++WordCopyPacket.bytes mode (inputCopy mode l)++
      StringInit.bytes mode (ownerPC mode l) l.ttape)
    (WordCopyPacket.bytes mode (transitionCopy mode l)) (TerminalMarker.bytes mode (markerPC mode l))
    (by simpa only [Initial,bytes,List.append_assoc] using initial)
  have location : l.start+(DwordArithmetic.encode (store mode l)++WordCopyPacket.bytes mode (inputCopy mode l)++
      StringInit.bytes mode (ownerPC mode l) l.ttape).length=(transitionCopy mode l).start := by
    have ownerLen : (StringInit.bytes mode (ownerPC mode l) l.ttape).length=StringCodec.initialSize mode := StringCodec.initial_length mode _ _ _
    rw [List.length_append,List.length_append,DwordArithmetic.encode_length,WordCopyPacket.bytes_length,ownerLen]
    simp only [store,DwordArithmetic.length,ownerPC,ConversionLayout.endpoint,inputCopy,transitionCopy,Nat.add_assoc]
  rw [location] at packet
  exact packet

theorem marker_current (mode : Mode) (l : Layout) (memory : ByteMemory.Memory)
    (initial : Initial mode l memory) :
    ByteMemory.bytesAt memory (markerPC mode l) 10=TerminalMarker.bytes mode (markerPC mode l) := by
  have packet:=ByteWindow.packet memory l.start
    (DwordArithmetic.encode (store mode l)++WordCopyPacket.bytes mode (inputCopy mode l)++
      StringInit.bytes mode (ownerPC mode l) l.ttape++WordCopyPacket.bytes mode (transitionCopy mode l))
    (TerminalMarker.bytes mode (markerPC mode l)) []
    (by simpa only [Initial,bytes,List.append_nil] using initial)
  have location : l.start+(DwordArithmetic.encode (store mode l)++WordCopyPacket.bytes mode (inputCopy mode l)++
      StringInit.bytes mode (ownerPC mode l) l.ttape++WordCopyPacket.bytes mode (transitionCopy mode l)).length=markerPC mode l := by
    have ownerLen : (StringInit.bytes mode (ownerPC mode l) l.ttape).length=StringCodec.initialSize mode := StringCodec.initial_length mode _ _ _
    rw [List.length_append,List.length_append,List.length_append,DwordArithmetic.encode_length,
      WordCopyPacket.bytes_length,WordCopyPacket.bytes_length,ownerLen]
    simp only [store,DwordArithmetic.length,markerPC,ownerPC,ConversionLayout.endpoint,inputCopy,transitionCopy,Nat.add_assoc]
  rw [location,TerminalMarker.length] at packet
  exact packet
end SmcTuring.Appendix.Listing8ResetPackets

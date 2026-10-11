module
public import SmcTuring.Appendix.Listing8JumpReturn

public section
namespace SmcTuring.Appendix.Listing8EntryPackets
open Native

theorem stack_packet (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin) :
    ByteMemory.bytesAt memory origin (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode origin := by
  have first:=ByteWindow.packet memory origin [] (Listing4Boot.bytes mode origin)
    (Listing4TargetLayout.bytes mode origin (Listing4JumpLayout.beginPC mode origin)) (by
      simp only [List.nil_append]
      change ByteMemory.bytesAt _ origin (Listing4EntryLayout.bytes mode origin).length=Listing4EntryLayout.bytes mode origin
      rw [Listing4EntryLayout.bytes_length];exact current)
  have code : ByteMemory.bytesAt memory origin (Listing4Boot.size mode)=Listing4Boot.bytes mode origin := by
    simpa only [List.length_nil,Nat.add_zero,Listing4Boot.bytes_length] using first
  exact Listing4Boot.stack_packet mode origin _ code

theorem begin_packet (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin) :
    ByteMemory.bytesAt memory (Listing8BootImage.beginPC mode origin) (Listing4TargetLayout.size mode)=
      Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin) := by
  have packet:=ByteWindow.packet memory origin (Listing4Boot.bytes mode origin)
    (Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin)) [] (by
      simp only [List.append_nil]
      change ByteMemory.bytesAt _ origin (Listing4EntryLayout.bytes mode origin).length=Listing4EntryLayout.bytes mode origin
      rw [Listing4EntryLayout.bytes_length];exact current)
  have typed : ByteMemory.bytesAt memory (origin+Listing4Boot.size mode) (Listing4TargetLayout.size mode)=
      Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin) := by
    simpa only [Listing4Boot.bytes_length,Listing4TargetLayout.bytes_length] using packet
  rw [←Listing4Boot.endpoint] at typed
  exact typed

theorem stptr (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory)
    (fits : origin+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin) :
    MixedMemory.getWord mode memory (Listing4StackLayout.stptr mode origin)=Arithmetic.encodeNat mode (Listing4StackLayout.stptr mode origin) :=
  Listing4StackLayout.initial_stptr mode origin memory fits (stack_packet mode origin memory current)

theorem return_field (mode : Mode) (origin : Nat) (memory : ByteMemory.Memory)
    (fits : origin+Listing4StackLayout.size mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin) :
    MixedMemory.getWord mode memory (Listing4StackLayout.returnField mode origin)=Arithmetic.encodeNat mode (Listing4StackLayout.stptr mode origin) :=
  Listing4TargetMemory.original_return mode origin memory fits (stack_packet mode origin memory current)

end SmcTuring.Appendix.Listing8EntryPackets

module
public import SmcTuring.Native.DwordOwner
public import SmcTuring.Native.MixedDword
public import SmcTuring.Native.BytePatch

public section
namespace SmcTuring.Native.DwordRetarget
open LittleEndian
abbrev Dword := BitVec 32

/-- The four printed MOVEMODEOFFS calls have do=2 and so=6. The source
owner is a ten-byte bare DWORD MOV; the destination is a live DWORD operand.
`here` cancels in the printed long-mode expression. -/
@[expose] def printed (mode : Mode) (here owner destination : Nat) : Dword :=
  match mode with
  | .x86 => BitVec.ofNat 32 (destination+6)
  | .x64 => BitVec.ofInt 32
      (((here : Int)-(owner : Int)+2)-((here : Int)-(destination : Int)+6))

@[expose] def ownerForm (mode : Mode) (owner target : Nat) (value : Dword) :=
  DwordArithmetic.located mode (.store 0 value) owner target
@[expose] def patchForm (mode : Mode) (patchPC owner destination : Nat) :=
  DwordArithmetic.located mode (.store 0 (printed mode patchPC owner destination)) patchPC (owner+2)
@[expose] def patched (mode : Mode) (patchPC owner destination : Nat) (state : Execution.State mode) :=
  DwordArithmetic.execute mode (patchForm mode patchPC owner destination) state

theorem owner_bytes (mode : Mode) (source : Nat) (value : Dword) :
    DwordOwner.bytes mode source value =
      DwordArithmetic.encode (.store (DwordOwner.form mode source value).displacement value) := rfl

theorem printed_displacement (mode : Mode) (here owner destination : Nat) :
    printed mode here owner destination = Relocation.memoryDisp mode (owner+10) (destination+6) := by
  cases mode with
  | x86 => rfl
  | x64 =>
    change BitVec.ofInt 32 (((here : Int)-(owner : Int)+2)-((here : Int)-(destination : Int)+6)) =
      BitVec.ofInt 32 (((destination+6 : Nat) : Int)-((owner+10 : Nat) : Int))
    congr 1
    omega

theorem displacement_patch (memory : ByteMemory.Memory) (owner : Nat) (old fresh value : Dword)
    (current : ByteMemory.bytesAt memory owner 10 = DwordArithmetic.encode (.store old value)) :
    ByteMemory.bytesAt (DwordCode.put memory (owner+2) fresh) owner 10 =
      DwordArithmetic.encode (.store fresh value) := by
  exact BytePatch.current memory owner [0xc7,0x05] (wordEncode 4 old) (wordEncode 4 fresh)
    (wordEncode 4 value) (by simp only [word_encode_length]) current

theorem patch_effect (mode : Mode) (patchPC owner destination : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode patchPC)
    (reach : mode = .x64 → Relocation.SignedDelta (patchPC+10) (owner+2))
    (fits : owner+2 < 2^(8*mode.wordBytes)) :
    patched mode patchPC owner destination state =
      { state with
        pc := Arithmetic.encodeNat mode (patchPC+10)
        memory := DwordCode.put state.memory (owner+2) (printed mode patchPC owner destination) } := by
  exact DwordArithmetic.located_effect mode (.store 0 (printed mode patchPC owner destination))
    patchPC (owner+2) state rfl location reach fits

theorem patched_current (mode : Mode) (patchPC owner destination : Nat) (old value : Dword)
    (state : Execution.State mode) (location : state.pc = Arithmetic.encodeNat mode patchPC)
    (reach : mode = .x64 → Relocation.SignedDelta (patchPC+10) (owner+2))
    (fits : owner+2 < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory owner 10 = DwordArithmetic.encode (.store old value)) :
    ByteMemory.bytesAt (patched mode patchPC owner destination state).memory owner 10 =
      DwordArithmetic.encode (ownerForm mode owner (destination+6) value) := by
  rw [patch_effect mode patchPC owner destination state location reach fits]
  have packet := displacement_patch state.memory owner old (printed mode patchPC owner destination) value current
  simpa only [printed_displacement,ownerForm,DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length]
    using packet

theorem patch_trace (mode : Mode) (patchPC owner destination : Nat) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode patchPC)
    (capacity : patchPC < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory patchPC 10 = DwordArithmetic.encode (patchForm mode patchPC owner destination)) :
    MixedDword.Trace mode state [.arithmetic (patchForm mode patchPC owner destination)]
      (patched mode patchPC owner destination state) := by
  refine .step ?_ (.nil _)
  rw [location,Arithmetic.encode_nat_toNat mode patchPC capacity]
  exact MixedDword.arithmetic_encoding mode state.memory patchPC _ current

theorem owner_effect (mode : Mode) (owner destination : Nat) (value : Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode owner)
    (reach : mode = .x64 → Relocation.SignedDelta (owner+10) (destination+6))
    (fits : destination+6 < 2^(8*mode.wordBytes)) :
    DwordArithmetic.execute mode (ownerForm mode owner (destination+6) value) state =
      { state with
        pc := Arithmetic.encodeNat mode (owner+10)
        memory := DwordCode.put state.memory (destination+6) value } := by
  exact DwordArithmetic.located_effect mode (.store 0 value) owner (destination+6) state rfl location reach fits

theorem owner_trace (mode : Mode) (owner destination : Nat) (value : Dword) (state : Execution.State mode)
    (location : state.pc = Arithmetic.encodeNat mode owner) (capacity : owner < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory owner 10 =
      DwordArithmetic.encode (ownerForm mode owner (destination+6) value)) :
    MixedDword.Trace mode state [.arithmetic (ownerForm mode owner (destination+6) value)]
      (DwordArithmetic.execute mode (ownerForm mode owner (destination+6) value) state) := by
  refine .step ?_ (.nil _)
  rw [location,Arithmetic.encode_nat_toNat mode owner capacity]
  exact MixedDword.arithmetic_encoding mode state.memory owner _ current

end SmcTuring.Native.DwordRetarget

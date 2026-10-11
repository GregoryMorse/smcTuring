module
public import SmcTuring.Native.StackMemory
public import SmcTuring.Native.StringInit
public import SmcTuring.Native.WordMemoryArithmetic

public section
namespace SmcTuring.Appendix.Listing4StackLayout
open Native LittleEndian
@[expose] def stptr (mode : Mode) (start : Nat) := start + match mode with | .x86 => 6 | .x64 => 16
/-- The return slot is the DEFDATA displacement in x86, svptr's MOFFS operand in x64. -/
@[expose] def returnField (mode : Mode) (start : Nat) := start + match mode with | .x86 => 2 | .x64 => 26
@[expose] def size : Mode → Nat | .x86 => 10 | .x64 => 34
@[expose] def first (start : Nat) : Native.Form .x64 :=
  .memory .exchangeAcc (Relocation.instructionDisp .x64 .exchangeAcc start (stptr .x64 start))
@[expose] def second (start : Nat) : Native.Form .x64 :=
  StackMemory.form .x64 .storeAcc (start+7) (stptr .x64 start)
@[expose] def third (start : Nat) : Native.Form .x64 := .moffs (Arithmetic.encodeNat .x64 (stptr .x64 start))
@[expose] def fourth (start : Nat) : Native.Form .x64 := .moffs (Arithmetic.encodeNat .x64 (stptr .x64 start))
@[expose] def bytes (mode : Mode) (start : Nat) : List Byte :=
  match mode with
  | .x86 => StringInit.bytes .x86 start (stptr .x86 start)
  | .x64 => Native.encode .x64 (first start) ++ Native.encode .x64 (second start) ++
      Native.encode .x64 (third start) ++ Native.encode .x64 (fourth start)
@[expose] def forms (mode : Mode) (start : Nat) : List (StringStack.Form mode) :=
  match mode with
  | .x86 => [.previous (.previous (.string (.initialize32
      (Arithmetic.encodeNat .x86 (stptr .x86 start)) (Arithmetic.encodeNat .x86 (stptr .x86 start)))))]
  | .x64 => [StringStack.native .x64 (first start),StringStack.native .x64 (second start),
      StringStack.native .x64 (third start),StringStack.native .x64 (fourth start)]

theorem first_displacement (start : Nat) : first start = .memory .exchangeAcc 9 := by
  have delta : Relocation.delta (start+7) (start+16) = 9 := by unfold Relocation.delta;omega
  unfold first Relocation.instructionDisp Relocation.memoryDisp Relocation.relative32 stptr
  rw [show Native.instructionLength .x64 (.memory .exchangeAcc 0)=7 from rfl,delta];rfl
theorem second_displacement (start : Nat) : second start = .memory .storeAcc 2 := by
  have delta : Relocation.delta (start+7+7) (start+16) = 2 := by unfold Relocation.delta;omega
  unfold second StackMemory.form Relocation.instructionDisp Relocation.memoryDisp Relocation.relative32 stptr
  rw [show Native.instructionLength .x64 (.memory .storeAcc 0)=7 from rfl,delta];rfl
theorem bytes_length (mode : Mode) (start : Nat) : (bytes mode start).length = size mode := by
  cases mode with
  | x86 => exact StringCodec.initial_length .x86 start _ _
  | x64 => rw [bytes,first_displacement,second_displacement];rfl
theorem stptr_fits (mode : Mode) (start : Nat) (fits : start+size mode < 2^(8*mode.wordBytes)) :
    stptr mode start+mode.wordBytes ≤ start+size mode := by cases mode <;> simp [stptr,size,Mode.wordBytes] <;> omega
theorem return_inside (mode : Mode) (start position : Nat)
    (inside : ByteMemory.Inside (returnField mode start) mode.wordBytes position) :
    ByteMemory.Inside start (size mode) position := by
  cases mode <;> simp [ByteMemory.Inside,returnField,size,Mode.wordBytes] at * <;> omega
theorem stptr_inside (mode : Mode) (start position : Nat)
    (inside : ByteMemory.Inside (stptr mode start) mode.wordBytes position) :
    ByteMemory.Inside start (size mode) position := by
  cases mode <;> simp [ByteMemory.Inside,stptr,size,Mode.wordBytes] at * <;> omega
theorem fields_separate (mode : Mode) (start : Nat) :
    returnField mode start+mode.wordBytes ≤ stptr mode start ∨ stptr mode start+mode.wordBytes ≤ returnField mode start := by
  cases mode <;> simp [returnField,stptr,Mode.wordBytes] <;> omega

theorem initial_stptr (mode : Mode) (start : Nat) (memory : ByteMemory.Memory)
    (fits : start+size mode < 2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt memory start (size mode) = bytes mode start) :
    MixedMemory.getWord mode memory (stptr mode start) = Arithmetic.encodeNat mode (stptr mode start) := by
  have targetFits : stptr mode start < 2^(8*mode.wordBytes) := by
    have bound := stptr_fits mode start fits;omega
  rw [←MixedMemory.load_nat mode memory _ targetFits]
  cases mode with
  | x86 => exact StringInit.initialized_pointer .x86 start _ memory fits current
  | x64 =>
    let a := Native.encode .x64 (first start)
    let b := Native.encode .x64 (second start)
    let address : BitVec 64 := Arithmetic.encodeNat .x64 (stptr .x64 start)
    have code : ByteMemory.bytesAt memory start (a++b++[0x48,0xa3]++wordEncode 8 address++Native.encode .x64 (fourth start)).length =
        a++b++[0x48,0xa3]++wordEncode 8 address++Native.encode .x64 (fourth start) := by
      change ByteMemory.bytesAt memory start (bytes .x64 start).length = bytes .x64 start
      rw [bytes_length];exact current
    have payload := ByteWindow.packet memory start (a++b++[0x48,0xa3]) (wordEncode 8 address)
      (Native.encode .x64 (fourth start)) (by simpa only [List.append_assoc] using code)
    have headerSize : (a++b++[0x48,0xa3]).length = 16 := by
      dsimp [a,b];rw [first_displacement,second_displacement];rfl
    rw [headerSize] at payload
    exact StringWindow.initial_word .x64 memory _ address targetFits payload

theorem initial_svptr (start : Nat) (memory : ByteMemory.Memory)
    (fits : start+34 < 2^64)
    (current : ByteMemory.bytesAt memory start 34 = bytes .x64 start) :
    MixedMemory.getWord .x64 memory (returnField .x64 start) = Arithmetic.encodeNat .x64 (stptr .x64 start) := by
  let leading := Native.encode .x64 (first start)++Native.encode .x64 (second start)++Native.encode .x64 (third start)++[0x48,0xa3]
  let address : BitVec 64 := Arithmetic.encodeNat .x64 (stptr .x64 start)
  have code : ByteMemory.bytesAt memory start (leading++wordEncode 8 address++[]).length = leading++wordEncode 8 address++[] := by
    simp only [List.append_nil]
    change ByteMemory.bytesAt memory start (bytes .x64 start).length = bytes .x64 start
    rw [bytes_length];exact current
  have payload := ByteWindow.packet memory start leading (wordEncode 8 address) [] code
  have headerSize : leading.length = 26 := by
    dsimp [leading];rw [first_displacement,second_displacement];rfl
  rw [headerSize] at payload
  have targetFits : returnField .x64 start < 2^64 := by dsimp [returnField];omega
  rw [←MixedMemory.load_nat .x64 memory _ targetFits]
  exact StringWindow.initial_word .x64 memory _ address targetFits payload
end SmcTuring.Appendix.Listing4StackLayout

module
public import SmcTuring.Native.StringDwordCopy

public section
namespace SmcTuring.Native.StringDwordXor
@[expose] def canonical (mode : Mode) (displacement : BitVec 32) : StringDword.Form mode :=
  match mode with
  | .x86 => StringDwordCopy.native .x86 (.memory .bitXor displacement)
  | .x64 => .xorAccumulator displacement

theorem encoding (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (displacement : BitVec 32)
    (current : ByteMemory.bytesAt memory pc 6 = DwordXor.encode displacement) :
    StringDword.fetch mode memory pc = some (canonical mode displacement) := by
  cases mode with
  | x86 => exact StringDwordCopy.native_encoding .x86 (.memory .bitXor displacement) memory pc current
  | x64 =>
    have noLength : StringForm.lengthOfBytes .x64 (ByteMemory.bytesAt memory pc 3) = none := by
      rw [←Fetch.bytes_at_take memory pc 6 3 (by decide),current]
      rfl
    have noString : StringForm.fetch .x64 memory pc = none := by rw [StringForm.fetch,noLength];rfl
    have noArithmetic : DwordArithmetic.packetSize (ByteMemory.bytesAt memory pc 2) = none := by
      rw [←Fetch.bytes_at_take memory pc 6 2 (by decide),current]
      rfl
    have first := congrArg (fun bytes : List LittleEndian.Byte => bytes[0]?) current
    change some (memory pc) = some (0x31 : LittleEndian.Byte) at first
    have tag := Option.some.inj first
    have taken : (LittleEndian.wordEncode 4 displacement).take 4 = LittleEndian.wordEncode 4 displacement := rfl
    have noMixed : MixedDword.fetch .x64 memory pc = none := by
      simp only [MixedDword.fetch.eq_def,noArithmetic,tag,reduceCtorEq]
      simp [DwordCode.fetch,DwordCode.packetSize,tag,current,DwordXor.encode,DwordCode.decode,
        Native.decodeCore,Native.operationOfTag,Native.decodeMemoryPayload,MemoryOp.trailer,taken]
    rw [StringDword.fetch,noString,noMixed,DwordXor.fetch_encoding .x64 memory pc displacement current]
    all_goals rfl

theorem execute (mode : Mode) (displacement : BitVec 32) (state : StringExecution.State mode) :
    StringDword.execute mode (canonical mode displacement) state =
      {state with principal := DwordXor.execute mode displacement state.principal} := by
  cases mode with
  | x86 => rw [canonical,StringDwordCopy.native_execute,DwordXor.native_x86]
  | x64 => rfl

end SmcTuring.Native.StringDwordXor

module
public import SmcTuring.Appendix.DivisionByteCode
public import SmcTuring.Native.ConversionOwnership
public import SmcTuring.X64.HalfFrame

public section
namespace SmcTuring.Appendix.InputOperand
open Native Native.Execution Native.LittleEndian

abbrev Dword := BitVec 32
/-- The patched first instruction of COMPARE32: DWORD SUB, imm32 at six.
Its encoded address word is absolute x86 or a long-mode RIP displacement. -/
@[expose] def sourceBytes (address symbol : Dword) : List Byte :=
  DivisionByteCode.encode (.subtractImmediate address symbol)
/-- The printed inputupdate DWORD XOR [AX+6],imm32, without REX.W.
REGIMMOFFS is three and the complete forced imm32 packet is seven bytes. -/
@[expose] def targetBytes (value : Dword) : List Byte := [0x81,0x70,0x06] ++ wordEncode 4 value
@[expose] def targetDecode (bytes : List Byte) : Option Dword :=
  if bytes.take 3 = [0x81,0x70,0x06] then wordDecode 4 (bytes.drop 3) else none

theorem source_length (address symbol : Dword) : (sourceBytes address symbol).length = 10 := by
  simp [sourceBytes,DivisionByteCode.encode]
theorem target_length (value : Dword) : (targetBytes value).length = 7 := by simp [targetBytes]
theorem target_roundtrip (value : Dword) : targetDecode (targetBytes value) = some value := by
  have taken : (targetBytes value).take 3 = [0x81,0x70,0x06] := rfl
  have dropped : (targetBytes value).drop 3 = wordEncode 4 value := rfl
  simp only [targetDecode,taken,dropped,ite_true,word_decode_encode]

/-- The declared operand's exact bytes determine its value, for arbitrary
backing memory and naturally addressed DWORD windows. -/
theorem read_payload (memory : ByteMemory.Memory) (pc : Nat) (leading : List Byte) (value : Dword) :
    ByteMemory.readWord .x86 (ByteMemory.putBytes memory pc (leading ++ wordEncode 4 value))
      (pc + leading.length) = some value := by
  have patch := ByteMemory.patch_payload memory pc leading (wordEncode 4 value) (wordEncode 4 value) rfl
  have loaded := ByteMemory.read_put_word .x86 (ByteMemory.putBytes memory pc (leading ++ wordEncode 4 value))
    (pc + leading.length) value
  change ByteMemory.readWord .x86
    (ByteMemory.putBytes (ByteMemory.putBytes memory pc (leading ++ wordEncode 4 value))
      (pc + leading.length) (wordEncode 4 value)) (pc + leading.length) = some value at loaded
  rwa [patch] at loaded

theorem current_source (memory : ByteMemory.Memory) (pc : Nat) (address symbol : Dword)
    (current : ByteMemory.bytesAt memory pc 10 = sourceBytes address symbol) :
    ByteMemory.readWord .x86 memory (pc + 6) = some symbol := by
  have kept := ByteMemory.put_current memory pc (sourceBytes address symbol)
    (by simpa only [source_length] using current)
  have loaded := read_payload memory pc ([0x81,0x2d] ++ wordEncode 4 address) symbol
  have leading : ([0x81,0x2d] ++ wordEncode 4 address).length = 6 := by simp
  change ByteMemory.readWord .x86 (ByteMemory.putBytes memory pc (sourceBytes address symbol)) _ = _ at loaded
  rwa [leading,kept] at loaded

theorem current_source_load (memory : ByteMemory.Memory) (pc : Nat) (address symbol : Dword)
    (fits : pc + 6 < 2 ^ 32)
    (current : ByteMemory.bytesAt memory pc 10 = sourceBytes address symbol) :
    load .x86 memory (Arithmetic.encodeNat .x86 (pc + 6)) = symbol := by
  have loaded := read_word_total .x86 memory (Arithmetic.encodeNat .x86 (pc + 6))
  rw [Arithmetic.encode_nat_toNat .x86 _ fits] at loaded
  exact Option.some.inj (loaded.symm.trans (current_source memory pc address symbol current))

theorem target_patch (memory : ByteMemory.Memory) (pc : Nat) (old fresh : Dword)
    (current : ByteMemory.bytesAt memory pc 7 = targetBytes old) :
    ByteMemory.putWord .x86 memory (pc + 3) fresh = ByteMemory.putBytes memory pc (targetBytes fresh) := by
  have kept := ByteMemory.put_current memory pc (targetBytes old) (by simpa only [target_length] using current)
  have patch := ByteMemory.patch_payload memory pc [0x81,0x70,0x06] (wordEncode 4 old) (wordEncode 4 fresh)
    (by simp only [word_encode_length])
  change ByteMemory.putWord .x86 (ByteMemory.putBytes memory pc (targetBytes old)) (pc+3) fresh =
    ByteMemory.putBytes memory pc (targetBytes fresh) at patch
  rwa [kept] at patch

theorem patched_target (memory : ByteMemory.Memory) (pc : Nat) (old fresh : Dword)
    (current : ByteMemory.bytesAt memory pc 7 = targetBytes old) :
    ByteMemory.bytesAt (ByteMemory.putWord .x86 memory (pc + 3) fresh) pc 7 = targetBytes fresh := by
  rw [target_patch memory pc old fresh current]
  simpa only [target_length] using ByteMemory.bytes_at_put memory pc (targetBytes fresh)

/-- Positive correction of Listing 8's source operand. The same three
instructions read source-PC+6 and write target-PC+3; later target bytes are
derived from the current source, not an assumed cached symbol. -/
theorem copy_correct (layout : ConversionLayout.Layout) (valid : ConversionLayout.Admissible .x86 layout)
    (state : Native.Execution.State .x86)
    (entry : state.pc = Arithmetic.encodeNat .x86 layout.start)
    (intact : ControlImage.Intact .x86 (ConversionLayout.entries .x86 layout) state.memory)
    (sourcePC targetPC : Nat) (sourceField : layout.source = sourcePC + 6)
    (targetField : layout.destination = targetPC + 3) (address symbol old : Dword)
    (currentSource : ByteMemory.bytesAt state.memory sourcePC 10 = sourceBytes address symbol)
    (currentTarget : ByteMemory.bytesAt state.memory targetPC 7 = targetBytes old) :
    Fetch.Trace .x86 state (ConversionLayout.program .x86 layout) (ConversionEffects.finish .x86 layout state) ∧
    (ConversionEffects.finish .x86 layout state).memory = ByteMemory.putWord .x86 state.memory (targetPC+3) symbol ∧
    ByteMemory.bytesAt (ConversionEffects.finish .x86 layout state).memory targetPC 7 = targetBytes symbol ∧
    targetDecode (ByteMemory.bytesAt (ConversionEffects.finish .x86 layout state).memory targetPC 7) = some symbol ∧
    (ConversionEffects.finish .x86 layout state).accumulator = state.accumulator ∧
    (ConversionEffects.finish .x86 layout state).stack = state.stack ∧
    (ConversionEffects.finish .x86 layout state).carry = state.carry := by
  have sourceFits : sourcePC + 6 < 2 ^ 32 := by
    have bound := valid.sourceFits
    change layout.source + 4 ≤ 2 ^ 32 at bound
    rw [sourceField] at bound
    omega
  have loaded : load .x86 state.memory (Arithmetic.encodeNat .x86 layout.source) = symbol := by
    rw [sourceField]
    exact current_source_load state.memory sourcePC address symbol sourceFits currentSource
  have memory : (ConversionEffects.finish .x86 layout state).memory =
      ByteMemory.putWord .x86 state.memory (targetPC+3) symbol := by
    rw [ConversionEffects.effect .x86 layout valid state entry,loaded,targetField]
  have packet : ByteMemory.bytesAt (ConversionEffects.finish .x86 layout state).memory targetPC 7 = targetBytes symbol := by
    rw [memory]
    exact patched_target state.memory targetPC old symbol currentTarget
  have result := ConversionImage.correct .x86 layout valid state intact entry
  exact ⟨result.1,memory,packet,by rw [packet,target_roundtrip],
    result.2.2.2.1,result.2.2.2.2.1,result.2.2.2.2.2.1⟩

theorem copy_frame (layout : ConversionLayout.Layout) (valid : ConversionLayout.Admissible .x86 layout)
    (state : Native.Execution.State .x86) (entry : state.pc = Arithmetic.encodeNat .x86 layout.start)
    (position : Nat) (outside : ¬ByteMemory.Inside layout.destination 4 position) :
    (ConversionEffects.finish .x86 layout state).memory position = state.memory position :=
  ConversionEffects.frame .x86 layout valid state entry position outside

/-- Both header/operand regions are actual code packets. All three stores
target their complete corresponding imm32 words, including unchanged writes. -/
theorem copy_pure (layout : ConversionLayout.Layout) (valid : ConversionLayout.Admissible .x86 layout)
    (state : Native.Execution.State .x86) (entry : state.pc = Arithmetic.encodeNat .x86 layout.start)
    (sourcePC targetPC : Nat) (sourceField : layout.source = sourcePC+6) (targetField : layout.destination = targetPC+3) :
    Writes.OwnedRun .x86 (fun word => word.toNat = sourcePC+6 ∨ word.toNat = targetPC+3)
      (ConversionLayout.program .x86 layout) state := by
  apply ConversionOwnership.supported_run .x86 layout valid state entry
  · exact Or.inl ((ConversionLayout.source_toNat .x86 layout valid).trans sourceField)
  · exact Or.inr ((ConversionLayout.destination_toNat .x86 layout valid).trans targetField)

theorem operand_windows (sourcePC targetPC position : Nat) :
    (ByteMemory.Inside (sourcePC+6) 4 position → ByteMemory.Inside sourcePC 10 position) ∧
    (ByteMemory.Inside (targetPC+3) 4 position → ByteMemory.Inside targetPC 7 position) := by
  unfold ByteMemory.Inside
  omega

/-- The published USEWORD32 contract uses logical DWORD fields in either
mode. A source label at an instruction header therefore needs IMMOFFS. -/
theorem word_effect (sourcePC targetPC : Nat) (state : Machine32.State)
    (separate : targetPC+3 ≠ sourcePC+6) :
    X64.HalfFrame.run (X64.HalfFrame.useWord .move (targetPC+3) (sourcePC+6)) state =
      Machine32.put state (targetPC+3) (state.memory (sourcePC+6)) state.carry :=
  X64.HalfFrame.use_effect .move _ _ state separate

theorem word_symbol (sourcePC targetPC : Nat) (state : Machine32.State) (symbol : Dword)
    (separate : targetPC+3 ≠ sourcePC+6) (current : state.memory (sourcePC+6) = symbol) :
    (X64.HalfFrame.run (X64.HalfFrame.useWord .move (targetPC+3) (sourcePC+6)) state).memory (targetPC+3) = symbol := by
  rw [X64.HalfFrame.use_target .move _ _ state separate,current]
  rfl

/-- Standard nonoverlapping prototype packets retain the entire source
instruction, including its header and address bytes, after the copy. -/
theorem source_code_frame (layout : ConversionLayout.Layout) (valid : ConversionLayout.Admissible .x86 layout)
    (state : Native.Execution.State .x86) (entry : state.pc = Arithmetic.encodeNat .x86 layout.start)
    (sourcePC targetPC : Nat) (targetField : layout.destination = targetPC+3)
    (apart : targetPC+7 ≤ sourcePC ∨ sourcePC+10 ≤ targetPC) :
    ByteMemory.bytesAt (ConversionEffects.finish .x86 layout state).memory sourcePC 10 =
      ByteMemory.bytesAt state.memory sourcePC 10 := by
  rw [ConversionEffects.effect .x86 layout valid state entry,targetField]
  apply ByteMemory.bytes_at_frame
  intro index
  have bound := index.isLt
  change ¬ByteMemory.Inside (targetPC+3) 4 (sourcePC+index.val)
  unfold ByteMemory.Inside
  omega

end SmcTuring.Appendix.InputOperand

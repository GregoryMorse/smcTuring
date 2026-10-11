module
public import SmcTuring.Native.StringTemplate

public section
namespace SmcTuring.Native.StringOperands
open StringExecution LittleEndian

@[expose] def exchange (mode : Mode) (destination : Bool) (pc field : Nat) : StringForm.Form mode :=
  .exchangeIndex destination (Relocation.memoryDisp mode (pc+StringCodec.exchangeSize mode) field)
@[expose] def subtract (mode : Mode) (pc field size : Nat) : StringForm.Form mode :=
  let displacement := Relocation.memoryDisp mode (pc+StringCodec.subSize mode size) field
  if size < 128 then .subtractSmall displacement (BitVec.ofNat 8 size)
  else .subtractFull displacement (BitVec.ofNat 32 size)

theorem exchange_encoding (mode : Mode) (destination : Bool) (pc field : Nat) :
    StringForm.encode mode (exchange mode destination pc field) = StringCodec.exchangeBytes mode destination pc field := rfl

theorem exchange_length (mode : Mode) (destination : Bool) (pc field : Nat) :
    StringForm.length mode (exchange mode destination pc field) = StringCodec.exchangeSize mode :=
  StringCodec.exchange_length mode destination pc field

theorem sign_extend_small (mode : Mode) (size : Nat) (small : size < 128) :
    (BitVec.ofNat 8 size).signExtend (8*mode.wordBytes) = Arithmetic.encodeNat mode size := by
  have sign : (BitVec.ofNat 8 size).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false sign]
  apply BitVec.eq_of_toNat_eq
  have capacity : size < 2^(8*mode.wordBytes) := by cases mode <;> simp [Mode.wordBytes] <;> omega
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : size < 2^8),Arithmetic.encodeNat,Nat.mod_eq_of_lt capacity]

theorem sign_extend_full (mode : Mode) (size : Nat) (fits : size < 2^31) :
    Execution.displacementWord mode (BitVec.ofNat 32 size) = Arithmetic.encodeNat mode size := by
  cases mode with
  | x86 => rfl
  | x64 =>
    have sign : (BitVec.ofNat 32 size).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      omega
    change (BitVec.ofNat 32 size).signExtend 64 = BitVec.ofNat 64 size
    rw [BitVec.signExtend_eq_setWidth_of_msb_false sign]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : size < 2^32),Nat.mod_eq_of_lt (by omega : size < 2^64)]

theorem subtract_encoding (mode : Mode) (pc field size : Nat) (fits : size < 2^31) :
    StringForm.encode mode (subtract mode pc field size) = StringCodec.subBytes mode pc field size := by
  unfold subtract StringCodec.subBytes
  split
  · rfl
  · cases mode <;> simp only [StringForm.encode,wordPrefix,wordEncode,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : size < 2^32)]

theorem subtract_length (mode : Mode) (pc field size : Nat) :
    StringForm.length mode (subtract mode pc field size) = StringCodec.subSize mode size := by
  unfold subtract StringForm.length StringCodec.subSize
  split <;> cases mode <;> simp [StringForm.encode,wordPrefix,StringCodec.exchangeSize]

theorem exchange_hits (mode : Mode) (destination : Bool) (pc field : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 -> Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field) :
    address mode (exchange mode destination pc field) state
      (Relocation.memoryDisp mode (pc+StringCodec.exchangeSize mode) field) = Arithmetic.encodeNat mode field := by
  unfold address nextPC
  rw [exchange_length,location]
  change Execution.memoryAddress mode (BitVec.ofNat (8*mode.wordBytes) pc+BitVec.ofNat (8*mode.wordBytes) (StringCodec.exchangeSize mode)) _ = _
  rw [BitVec.ofNat_add_ofNat]
  exact Relocation.memory_hits mode _ _ range

theorem subtract_next (mode : Mode) (pc field size : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode pc) :
    nextPC mode (subtract mode pc field size) state = Arithmetic.encodeNat mode (pc+StringCodec.subSize mode size) := by
  unfold nextPC
  rw [subtract_length,location]
  exact BitVec.ofNat_add_ofNat _ _

theorem subtract_effect (mode : Mode) (pc field size : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 -> Relocation.SignedDelta (pc+StringCodec.subSize mode size) field)
    (fits : size < 2^31) :
    execute mode (subtract mode pc field size) state = { state with
      principal := Execution.storeState mode state.principal (Arithmetic.encodeNat mode (pc+StringCodec.subSize mode size))
        (Arithmetic.encodeNat mode field) (Execution.load mode state.principal.memory (Arithmetic.encodeNat mode field)-Arithmetic.encodeNat mode size)
        (Arithmetic.unsignedBorrow (Execution.load mode state.principal.memory (Arithmetic.encodeNat mode field)) (Arithmetic.encodeNat mode size))} := by
  have hits : address mode (subtract mode pc field size) state
      (Relocation.memoryDisp mode (pc+StringCodec.subSize mode size) field) = Arithmetic.encodeNat mode field := by
    unfold address
    rw [subtract_next mode pc field size state location]
    exact Relocation.memory_hits mode _ _ range
  have next := subtract_next mode pc field size state location
  unfold subtract at hits next ⊢
  by_cases small : size < 128
  · simp only [ite_eq_left small] at hits next ⊢
    simp only [execute,hits,next,sign_extend_small mode size small]
  · simp only [ite_eq_right small] at hits next ⊢
    simp only [execute,hits,next,sign_extend_full mode size fits]

/-- Full-index cursor exchange with an address derived from placement. -/
theorem source_effect (mode : Mode) (pc field : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 -> Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (fieldFits : field < 2^(8*mode.wordBytes)) :
    execute mode (exchange mode false pc field) state = {state with
      principal := {state.principal with
        pc := Arithmetic.encodeNat mode (pc+StringCodec.exchangeSize mode)
        memory := ByteMemory.putWord mode state.principal.memory field state.sourceIndex}
      sourceIndex := Execution.load mode state.principal.memory (Arithmetic.encodeNat mode field)} := by
  change execute mode (.exchangeIndex false (Relocation.memoryDisp mode (pc+StringCodec.exchangeSize mode) field)) state = _
  rw [StringExecution.exchange_source mode state _ _ (exchange_hits mode false pc field state location range)]
  simp only [nextPC,location,Arithmetic.encode_nat_toNat mode field fieldFits]
  rw [show StringForm.length mode (.exchangeIndex false (Relocation.memoryDisp mode (pc+StringCodec.exchangeSize mode) field)) = StringCodec.exchangeSize mode from exchange_length mode false pc field]
  rw [show Arithmetic.encodeNat mode pc+Arithmetic.encodeNat mode (StringCodec.exchangeSize mode) = Arithmetic.encodeNat mode (pc+StringCodec.exchangeSize mode) from BitVec.ofNat_add_ofNat _ _]

theorem destination_effect (mode : Mode) (pc field : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode pc)
    (range : mode = .x64 -> Relocation.SignedDelta (pc+StringCodec.exchangeSize mode) field)
    (fieldFits : field < 2^(8*mode.wordBytes)) :
    execute mode (exchange mode true pc field) state = {state with
      principal := {state.principal with
        pc := Arithmetic.encodeNat mode (pc+StringCodec.exchangeSize mode)
        memory := ByteMemory.putWord mode state.principal.memory field state.destinationIndex}
      destinationIndex := Execution.load mode state.principal.memory (Arithmetic.encodeNat mode field)} := by
  change execute mode (.exchangeIndex true (Relocation.memoryDisp mode (pc+StringCodec.exchangeSize mode) field)) state = _
  rw [StringExecution.exchange_destination mode state _ _ (exchange_hits mode true pc field state location range)]
  simp only [nextPC,location,Arithmetic.encode_nat_toNat mode field fieldFits]
  rw [show StringForm.length mode (.exchangeIndex true (Relocation.memoryDisp mode (pc+StringCodec.exchangeSize mode) field)) = StringCodec.exchangeSize mode from exchange_length mode true pc field]
  rw [show Arithmetic.encodeNat mode pc+Arithmetic.encodeNat mode (StringCodec.exchangeSize mode) = Arithmetic.encodeNat mode (pc+StringCodec.exchangeSize mode) from BitVec.ofNat_add_ofNat _ _]

end SmcTuring.Native.StringOperands

module
public import SmcTuring.Native.RegionExecution

public section

namespace SmcTuring.Native.WindowBounds

open Execution MemoryRegion RegionExecution

/-- A shorter subwindow of a contained loaded window is also contained. -/
theorem contained_slice (region : Region) (address count offset length : Nat)
    (inside : region.Contains address count) (bounded : offset + length ≤ count) :
    region.Contains (address + offset) length := by
  rcases inside with ⟨lower, upper⟩
  constructor <;> omega

/-- The selected core classifier cannot request an unbounded instruction window. -/
theorem core_length_bound (mode : Mode) (opcode : LittleEndian.Byte) (rest : List LittleEndian.Byte)
    (count : Nat) (classified : Fetch.coreLength mode opcode rest = some count) : count ≤ 15 := by
  by_cases moffs : opcode.toNat = 0xA3
  · cases mode <;> simp [Fetch.coreLength, BitVec.toNat_eq, moffs, wordPrefix, Mode.wordBytes] at classified <;> omega
  · cases rest with
    | nil => simp [Fetch.coreLength, BitVec.toNat_eq, moffs] at classified
    | cons modrm payload =>
      by_cases exchange : opcode.toNat = 0x87 ∧ modrm.toNat = 0x00
      · cases mode <;> simp [Fetch.coreLength, BitVec.toNat_eq, exchange, wordPrefix] at classified <;> omega
      · have core : ((operationOfTag opcode modrm).bind fun operation =>
            if operation = .callIndirect then none
            else some ((operation.prefix mode).length + 6 + operation.trailer.length)) = some count := by
          simpa [Fetch.coreLength, BitVec.toNat_eq, moffs, exchange] using classified
        cases tagged : operationOfTag opcode modrm with
        | none => simp only [tagged, Option.bind_none, reduceCtorEq] at core
        | some operation =>
          simp only [tagged, Option.bind_some] at core
          by_cases rejected : operation = .callIndirect
          · simp only [rejected, ite_true, reduceCtorEq] at core
          · have equal : (operation.prefix mode).length + 6 + operation.trailer.length = count := by
              exact Option.some.inj (by simpa only [rejected, ite_false] using core)
            rw [←equal]
            exact instruction_length_bound mode (.memory operation 0)

/-- All selected packet lengths are at most the architectural 15-byte bound,
even for headers whose full packet will subsequently fail to decode. -/
theorem classified_length_bound (mode : Mode) (bytes : List LittleEndian.Byte) (count : Nat)
    (classified : Fetch.lengthOfBytes mode bytes = some count) : count ≤ 15 := by
  cases bytes with
  | nil => simp only [Fetch.lengthOfBytes, reduceCtorEq] at classified
  | cons opcode rest =>
    by_cases relative : opcode.toNat = 0xE8
    · simp [Fetch.lengthOfBytes, BitVec.toNat_eq, relative] at classified; omega
    · by_cases indirect : opcode.toNat = 0xFF
      · cases rest with
        | nil => simp [Fetch.lengthOfBytes, BitVec.toNat_eq, indirect] at classified
        | cons modrm payload =>
          by_cases accepted : modrm.toNat = 0x15
          · simp [Fetch.lengthOfBytes, BitVec.toNat_eq, indirect, accepted] at classified; omega
          · simp [Fetch.lengthOfBytes, BitVec.toNat_eq, indirect, accepted] at classified
      · cases mode with
        | x86 =>
          apply core_length_bound .x86 opcode rest count
          simpa [Fetch.lengthOfBytes, BitVec.toNat_eq, relative, indirect] using classified
        | x64 =>
          by_cases rex : opcode.toNat = 0x48
          · cases rest with
            | nil => simp [Fetch.lengthOfBytes, BitVec.toNat_eq, rex] at classified
            | cons core payload =>
              apply core_length_bound .x64 core payload count
              simpa [Fetch.lengthOfBytes, BitVec.toNat_eq, relative, indirect, rex] using classified
          · simp [Fetch.lengthOfBytes, BitVec.toNat_eq, relative, indirect, rex] at classified

/-- Static containment of fifteen bytes covers automatic live-header fetch;
no expected form, packet encoding or future fetch result is a premise. -/
theorem fetch_within (mode : Mode) (region : Region) (state : State mode)
    (window : region.Contains state.pc.toNat 15) : FetchWithin mode region state := by
  refine ⟨by simpa only [Nat.add_zero] using contained_slice region _ 15 0 3 window (by decide), ?_⟩
  cases classified : Fetch.lengthOfBytes mode (ByteMemory.bytesAt state.memory state.pc.toNat 3) with
  | none => trivial
  | some count =>
    have bound := classified_length_bound mode _ count classified
    simpa only [Nat.add_zero] using contained_slice region _ 15 0 count window (by simpa only [Nat.zero_add] using bound)

/-- Static code and data bounds imply the complete live step footprint. -/
theorem safe (mode : Mode) (region : Region) (form : Form mode) (state : State mode)
    (code : region.Contains state.pc.toNat 15) (read : ReadWithin mode region form state)
    (written : region.Contains (Writes.address mode form state).toNat mode.wordBytes) :
    Safe mode region form state := ⟨fetch_within mode region state code, read, written⟩


/-- Static footprint certificates compose at their actual executed boundary. -/
theorem safe_run_append (mode : Mode) (region : Region) (first second : List (Form mode)) (state : State mode)
    (leading : SafeRun mode region first state)
    (trailing : SafeRun mode region second (runForms mode first state)) :
    SafeRun mode region (first ++ second) state := by
  induction first generalizing state with
  | nil => exact trailing
  | cons form rest ih =>
    exact ⟨leading.1, ih (execute mode form state) leading.2 trailing⟩

end SmcTuring.Native.WindowBounds

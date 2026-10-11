module
public import SmcTuring.Native.ReaderView

public section

namespace SmcTuring.Native.CallsImage

open Execution ControlImage

inductive Transfer where
  | relative (target : Nat)
  | indirect (field : Nat)

@[expose] def oneSize : Mode -> Nat | .x86 => 6 | .x64 => 7
@[expose] def resetSize : Mode -> Nat | .x86 => 12 | .x64 => 14
@[expose] def totalSize (mode : Mode) (transfer : Transfer) : Nat :=
  resetSize mode + match transfer with | .relative _ => 5 | .indirect _ => 6

@[expose] def firstDisp (mode : Mode) (start top : Nat) : BitVec 32 :=
  Relocation.instructionDisp mode .exchangeStack start top

@[expose] def secondDisp (mode : Mode) (start top : Nat) : BitVec 32 :=
  Relocation.instructionDisp mode .storeStack (start + oneSize mode) top

@[expose] def callTarget (mode : Mode) (start : Nat) : Transfer -> Calls.Target
  | .relative target => .relative (Relocation.relative32 (start + resetSize mode + 5) target)
  | .indirect field => .indirect (Relocation.instructionDisp mode .callIndirect (start + resetSize mode) field)

@[expose] def packets (mode : Mode) (start top : Nat) (transfer : Transfer) : List (Packet mode) :=
  [.fixed (.memory .exchangeStack (firstDisp mode start top)),
    .fixed (.memory .storeStack (secondDisp mode start top)), .fixed ((callTarget mode start transfer).form mode)]

@[expose] def firstEntry (mode : Mode) (start top : Nat) : Entry mode :=
  { pc := start, packet := .fixed (.memory .exchangeStack (firstDisp mode start top)) }

@[expose] def secondEntry (mode : Mode) (start top : Nat) : Entry mode :=
  { pc := start + oneSize mode, packet := .fixed (.memory .storeStack (secondDisp mode start top)) }

@[expose] def callEntry (mode : Mode) (start : Nat) (transfer : Transfer) : Entry mode :=
  { pc := start + resetSize mode, packet := .fixed ((callTarget mode start transfer).form mode) }

structure Ranges (mode : Mode) (start top : Nat) (transfer : Transfer) : Prop where
  first : mode = .x64 -> Relocation.SignedDelta (start + oneSize mode) top
  second : mode = .x64 -> Relocation.SignedDelta (start + resetSize mode) top
  call : match transfer with
    | .relative target => Relocation.SignedDelta (start + resetSize mode + 5) target
    | .indirect field => mode = .x64 -> Relocation.SignedDelta (start + resetSize mode + 6) field

theorem packet_size (mode : Mode) (start top : Nat) (transfer : Transfer) :
    ControlPacking.size mode (packets mode start top transfer) = totalSize mode transfer := by
  cases mode <;> cases transfer <;> rfl

theorem placed_roles (mode : Mode) (start top : Nat) (transfer : Transfer) :
    ControlPacking.place mode start (packets mode start top transfer) =
      [firstEntry mode start top, secondEntry mode start top, callEntry mode start transfer] := by
  cases mode <;> cases transfer <;>
    simp [ControlPacking.place, packets, Packet.bytes, encode, MemoryOp.prefix, MemoryOp.trailer,
      wordPrefix, LittleEndian.wordEncode, Calls.Target.form, callTarget,
      firstEntry, secondEntry, callEntry, oneSize, resetSize, Nat.add_assoc]

theorem exchange_pc (mode : Mode) (start top : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    (Calls.exchanged mode state (firstDisp mode start top)).pc = Arithmetic.encodeNat mode (start + oneSize mode) := by
  have length : instructionLength mode (.memory .exchangeStack (firstDisp mode start top)) = oneSize mode := by
    cases mode <;> rfl
  change state.pc + Arithmetic.encodeNat mode (instructionLength mode (.memory .exchangeStack (firstDisp mode start top))) = _
  rw [location, length]
  exact BitVec.ofNat_add_ofNat start (oneSize mode)

theorem reset_pc (mode : Mode) (start top : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    (Calls.reset mode state (firstDisp mode start top) (secondDisp mode start top)).pc =
      Arithmetic.encodeNat mode (start + resetSize mode) := by
  have next : (Calls.reset mode state (firstDisp mode start top) (secondDisp mode start top)).pc =
      (Calls.exchanged mode state (firstDisp mode start top)).pc + Arithmetic.encodeNat mode (oneSize mode) := by
    cases mode <;> rfl
  rw [next, exchange_pc mode start top state location]
  unfold Arithmetic.encodeNat
  rw [BitVec.ofNat_add_ofNat]
  congr 1
  cases mode <;> simp [oneSize, resetSize, Nat.add_assoc]

theorem return_next (mode : Mode) (start top : Nat) (transfer : Transfer) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) :
    nextPC mode ((callTarget mode start transfer).form mode)
      (Calls.reset mode state (firstDisp mode start top) (secondDisp mode start top)) =
        Arithmetic.encodeNat mode (start + totalSize mode transfer) := by
  unfold nextPC
  rw [reset_pc mode start top state location]
  unfold Arithmetic.encodeNat
  rw [BitVec.ofNat_add_ofNat]
  congr 1
  cases mode <;> cases transfer <;>
    simp [instructionLength, callTarget, Calls.Target.form, MemoryOp.prefix, MemoryOp.trailer,
      resetSize, totalSize, Nat.add_assoc]

theorem reset_ready (mode : Mode) (start top : Nat) (transfer : Transfer) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top transfer) :
    Calls.ResetReady mode state (Arithmetic.encodeNat mode top) (firstDisp mode start top) (secondDisp mode start top) := by
  constructor
  · apply Relocation.instruction_memory_hits mode .exchangeStack start top state location
    have length : instructionLength mode (.memory .exchangeStack 0) = oneSize mode := by cases mode <;> rfl
    simpa only [length] using ranges.first
  · apply Relocation.instruction_memory_hits mode .storeStack (start + oneSize mode) top _
      (exchange_pc mode start top state location)
    have next : start + oneSize mode + instructionLength mode (.memory .storeStack 0) = start + resetSize mode := by
      cases mode <;> simp [oneSize, resetSize, instructionLength, MemoryOp.prefix, MemoryOp.trailer, wordPrefix, Nat.add_assoc]
    simpa only [next] using ranges.second

theorem stack_ready (mode : Mode) (start top slot : Nat) (transfer : Transfer) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top transfer)
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes) :
    Calls.StackReady mode state (Arithmetic.encodeNat mode top) (Arithmetic.encodeNat mode slot)
      (firstDisp mode start top) (secondDisp mode start top) :=
  ⟨reset_ready mode start top transfer state location ranges, value⟩

theorem indirect_hits (mode : Mode) (start top field : Nat) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top (.indirect field)) :
    memoryAddress mode (nextPC mode ((callTarget mode start (.indirect field)).form mode)
      (Calls.reset mode state (firstDisp mode start top) (secondDisp mode start top)))
      (Relocation.instructionDisp mode .callIndirect (start + resetSize mode) field) = Arithmetic.encodeNat mode field := by
  apply Relocation.instruction_memory_hits mode .callIndirect (start + resetSize mode) field _
    (reset_pc mode start top state location)
  have length : instructionLength mode (.memory .callIndirect 0) = 6 := by cases mode <;> rfl
  simpa only [length] using ranges.call

theorem reached_positions (mode : Mode) (start top : Nat) (transfer : Transfer) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start)
    (fits : start + totalSize mode transfer < 2 ^ (8 * mode.wordBytes)) :
    And (state.pc.toNat = start)
      (And ((Calls.exchanged mode state (firstDisp mode start top)).pc.toNat = (secondEntry mode start top).pc)
        ((Calls.reset mode state (firstDisp mode start top) (secondDisp mode start top)).pc.toNat =
          (callEntry mode start transfer).pc)) := by
  have startFits : start < 2 ^ (8 * mode.wordBytes) := by omega
  have firstFits : start + oneSize mode < 2 ^ (8 * mode.wordBytes) := by
    cases mode <;> cases transfer <;> simp [oneSize, resetSize, totalSize, Mode.wordBytes] at * <;> omega
  have resetFits : start + resetSize mode < 2 ^ (8 * mode.wordBytes) := by
    unfold totalSize at fits
    cases transfer <;> omega
  rw [location, exchange_pc mode start top state location, reset_pc mode start top state location]
  exact ⟨Arithmetic.encode_nat_toNat mode start startFits,
    Arithmetic.encode_nat_toNat mode _ firstFits, Arithmetic.encode_nat_toNat mode _ resetFits⟩

/-- Fixed reset/CALL packets are fetched from the global current image, with
resolved operands and no supplied fetch or packet-length premises. -/
theorem trace (mode : Mode) (start top origin gridBase : Nat) (transfer : Transfer)
    (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top transfer)
    (fits : start + totalSize mode transfer < 2 ^ (8 * mode.wordBytes))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : origin + SpacedPacking.size mode whole <= gridBase - moffsOperandOffset mode)
    (within : Fragment.Within mode (ControlPacking.place mode start (packets mode start top transfer))
      (SpacedPacking.place mode origin whole))
    (intact : SpacedCombinedImage.Intact mode whole origin gridBase state.memory)
    (topOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode top)) :
    Fetch.Trace mode state (Calls.program mode (firstDisp mode start top) (secondDisp mode start top) (callTarget mode start transfer))
      (Calls.called mode state (firstDisp mode start top) (secondDisp mode start top) (callTarget mode start transfer)) := by
  have firstMember : List.Mem (firstEntry mode start top) (ControlPacking.place mode start (packets mode start top transfer)) := by
    rw [placed_roles]; exact List.Mem.head _
  have secondMember : List.Mem (secondEntry mode start top) (ControlPacking.place mode start (packets mode start top transfer)) := by
    rw [placed_roles]; exact List.Mem.tail _ (List.Mem.head _)
  have callMember : List.Mem (callEntry mode start transfer) (ControlPacking.place mode start (packets mode start top transfer)) := by
    rw [placed_roles]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have positions := reached_positions mode start top transfer state location fits
  have ready := reset_ready mode start top transfer state location ranges
  have exchangedIntact : SpacedCombinedImage.Intact mode whole origin gridBase (Calls.exchanged mode state (firstDisp mode start top)).memory := by
    apply SpacedCombinedImage.execute_intact mode whole origin gridBase state (.memory .exchangeStack (firstDisp mode start top)) enough gap intact
    change SpacedCombinedImage.Owned mode whole origin gridBase
      (memoryAddress mode (nextPC mode (.memory .exchangeStack (firstDisp mode start top)) state) (firstDisp mode start top))
    rw [ready.firstHits]; exact topOwned
  apply Calls.trace_of_fetches
  · rw [positions.1]
    exact fetch_current mode (firstEntry mode start top) state.memory (intact.1 _ (within _ firstMember))
  · rw [positions.2.1]
    exact fetch_current mode (secondEntry mode start top) _ (exchangedIntact.1 _ (within _ secondMember))
  · rw [Calls.reset_memory mode state _ _ _ ready, positions.2.2]
    exact fetch_current mode (callEntry mode start transfer) state.memory (intact.1 _ (within _ callMember))

theorem owned_run (mode : Mode) (start top slot origin gridBase : Nat) (transfer : Transfer)
    (whole : List (SpacedPacking.Piece mode)) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top transfer)
    (value : load mode state.memory (Arithmetic.encodeNat mode top) =
      Arithmetic.encodeNat mode slot + Arithmetic.encodeNat mode mode.wordBytes)
    (topOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode top))
    (slotOwned : SpacedCombinedImage.Owned mode whole origin gridBase (Arithmetic.encodeNat mode slot)) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode whole origin gridBase)
      (Calls.program mode (firstDisp mode start top) (secondDisp mode start top) (callTarget mode start transfer)) state :=
  Calls.owned_run mode state _ _ _ _ _ (stack_ready mode start top slot transfer state location ranges value)
    (SpacedCombinedImage.Owned mode whole origin gridBase) topOwned slotOwned

theorem target_pc (mode : Mode) (start top : Nat) (transfer : Transfer) (state : State mode)
    (location : state.pc = Arithmetic.encodeNat mode start) (ranges : Ranges mode start top transfer) :
    (Calls.called mode state (firstDisp mode start top) (secondDisp mode start top) (callTarget mode start transfer)).pc =
      (match transfer with
       | .relative target => Arithmetic.encodeNat mode target
       | .indirect field => load mode state.memory (Arithmetic.encodeNat mode field)) := by
  cases transfer with
  | relative target =>
    change nextPC mode ((callTarget mode start (.relative target)).form mode)
      (Calls.reset mode state (firstDisp mode start top) (secondDisp mode start top)) +
      displacementWord mode (Relocation.relative32 (start + resetSize mode + 5) target) = _
    rw [return_next mode start top (.relative target) state location]
    have length : start + totalSize mode (.relative target) = start + resetSize mode + 5 := by simp [totalSize, Nat.add_assoc]
    rw [length]
    exact Relocation.add_relative32 mode _ target ranges.call
  | indirect field =>
    apply Calls.indirect_target mode state (Arithmetic.encodeNat mode top) (Arithmetic.encodeNat mode field)
      (firstDisp mode start top) (secondDisp mode start top) _ (reset_ready mode start top (.indirect field) state location ranges)
    exact indirect_hits mode start top field state location ranges

end SmcTuring.Native.CallsImage

module
public import SmcTuring.Native.ReadInvocationImage

public section

namespace SmcTuring.Native.ScalarImage

open Execution ControlImage

/-- Fixed memory-destination forms used by the native guard and source blocks. -/
inductive Op where
  | store | add | subtract | bitXor | bitAnd | subtractBorrowZero
  deriving DecidableEq

@[expose] def memoryOp : Op -> MemoryOp
  | .store => .storeAcc
  | .add => .add
  | .subtract => .subtract
  | .bitXor => .bitXor
  | .bitAnd => .bitAnd
  | .subtractBorrowZero => .subtractBorrowZero

structure Layout (mode : Mode) where
  start : Nat
  target : Nat
  origin : Nat
  gridBase : Nat
  whole : List (SpacedPacking.Piece mode)

/-- MASM selects the short A3 accumulator store in x86. The x64 fixed
store uses RIP-relative 89; all other scalar operations use ModRM forms. -/
@[expose] def size (mode : Mode) (op : Op) : Nat :=
  match mode, op with
  | .x86, .store => instructionLength .x86 (.moffs 0)
  | _, _ => instructionLength mode (.memory (memoryOp op) 0)

@[expose] def displacement (mode : Mode) (op : Op) (layout : Layout mode) : BitVec 32 :=
  Relocation.instructionDisp mode (memoryOp op) layout.start layout.target
@[expose] def form : (mode : Mode) -> Op -> Layout mode -> Form mode
  | .x86, .store, layout => .moffs (Arithmetic.encodeNat .x86 layout.target)
  | .x86, op, layout => .memory (memoryOp op) (displacement .x86 op layout)
  | .x64, op, layout => .memory (memoryOp op) (displacement .x64 op layout)

@[expose] def entry (mode : Mode) (op : Op) (layout : Layout mode) : Entry mode := ⟨layout.start, .fixed (form mode op layout)⟩
@[expose] def program (mode : Mode) (op : Op) (layout : Layout mode) : List (Form mode) := [form mode op layout]
@[expose] def finish (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) : State mode := execute mode (form mode op layout) state

@[expose] def value (mode : Mode) (op : Op) (prior accumulator : Word mode) (carry : Bool) : Word mode :=
  match op with
  | .store => accumulator
  | .add => prior + accumulator
  | .subtract => prior - accumulator
  | .bitXor => prior ^^^ accumulator
  | .bitAnd => prior &&& accumulator
  | .subtractBorrowZero => prior - (if carry then 1 else 0)

@[expose] def carryValue (mode : Mode) (op : Op) (prior accumulator : Word mode) (carry : Bool) : Bool :=
  match op with
  | .store => carry
  | .add => BitVec.uaddOverflow prior accumulator
  | .subtract => Arithmetic.unsignedBorrow prior accumulator
  | .bitXor | .bitAnd => false
  | .subtractBorrowZero => decide (prior.toNat < (if carry then 1 else 0 : Nat))

structure Ready (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) : Prop where
  location : state.pc = Arithmetic.encodeNat mode layout.start
  range : mode = .x64 -> Relocation.SignedDelta (layout.start + size mode op) layout.target
  codeFits : layout.start + size mode op < 2 ^ (8 * mode.wordBytes)
  targetFits : layout.target < 2 ^ (8 * mode.wordBytes)
  enough : moffsOperandOffset mode <= layout.gridBase
  gap : layout.origin + SpacedPacking.size mode layout.whole <= layout.gridBase - moffsOperandOffset mode
  member : List.Mem (entry mode op layout) (SpacedPacking.place mode layout.origin layout.whole)
  intact : SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase state.memory
  owned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Arithmetic.encodeNat mode layout.target)

/-- A scalar's relocation, placement and ownership are static. Its executed
input state needs only the computed location and the maintained code image. -/
theorem transport_ready (mode : Mode) (op : Op) (layout : Layout mode) (original actual : State mode)
    (ready : Ready mode op layout original)
    (location : actual.pc = Arithmetic.encodeNat mode layout.start)
    (intact : SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase actual.memory) :
    Ready mode op layout actual :=
  ⟨location, ready.range, ready.codeFits, ready.targetFits, ready.enough, ready.gap,
    ready.member, intact, ready.owned⟩

theorem form_size (mode : Mode) (op : Op) (layout : Layout mode) : instructionLength mode (form mode op layout) = size mode op := by
  cases mode <;> cases op <;> rfl

theorem store_size (mode : Mode) : size mode .store = (match mode with | .x86 => 5 | .x64 => 7) := by cases mode <;> rfl

theorem sbb_size (mode : Mode) : size mode .subtractBorrowZero = (match mode with | .x86 => 7 | .x64 => 8) := by cases mode <;> rfl

theorem hits (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    memoryAddress mode (nextPC mode (form mode op layout) state) (displacement mode op layout) = Arithmetic.encodeNat mode layout.target := by
  cases mode with
  | x86 => rfl
  | x64 => exact Relocation.instruction_memory_hits .x64 (memoryOp op) layout.start layout.target state ready.location ready.range

theorem next_pc (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    nextPC mode (form mode op layout) state = Arithmetic.encodeNat mode (layout.start + size mode op) := by
  rw [Relocation.next_pc mode state _ layout.start ready.location, form_size]

theorem fetch (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    Fetch.fetch mode state.memory state.pc.toNat = some (form mode op layout) := by
  have fits : layout.start < 2 ^ (8 * mode.wordBytes) := by have bound := ready.codeFits; omega
  rw [ready.location, Arithmetic.encode_nat_toNat mode _ fits]
  exact ControlImage.fetch_current mode (entry mode op layout) state.memory (ready.intact.1 _ ready.member)

theorem trace (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    Fetch.Trace mode state (program mode op layout) (finish mode op layout state) :=
  .step (fetch mode op layout state ready) (.nil _)

theorem written_address (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    Writes.address mode (form mode op layout) state = Arithmetic.encodeNat mode layout.target := by
  cases mode <;> cases op <;> first | rfl | exact hits _ _ layout state ready

theorem owned_run (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase) (program mode op layout) state := by
  change And (SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase (Writes.address mode (form mode op layout) state)) True
  rw [written_address mode op layout state ready]
  exact ⟨ready.owned, trivial⟩

theorem pc (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).pc = Arithmetic.encodeNat mode (layout.start + size mode op) := by
  have effect : (finish mode op layout state).pc = nextPC mode (form mode op layout) state := by cases mode <;> cases op <;> rfl
  exact effect.trans (next_pc mode op layout state ready)

theorem position (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).pc.toNat = layout.start + size mode op := by
  rw [pc mode op layout state ready, Arithmetic.encode_nat_toNat mode _ ready.codeFits]

theorem memory_word_effect (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).memory = ByteMemory.putWord mode state.memory (Arithmetic.encodeNat mode layout.target).toNat
      (value mode op (load mode state.memory (Arithmetic.encodeNat mode layout.target)) state.accumulator state.carry) := by
  have address := hits mode op layout state ready
  cases mode <;> cases op <;> simp only [finish, form, memoryOp, execute] at address ⊢
  all_goals first | rfl | (rw [address]; rfl)

theorem memory_effect (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).memory = ByteMemory.putWord mode state.memory layout.target
      (value mode op (load mode state.memory (Arithmetic.encodeNat mode layout.target)) state.accumulator state.carry) := by
  rw [memory_word_effect mode op layout state ready, Arithmetic.encode_nat_toNat mode _ ready.targetFits]

theorem written_value (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    load mode (finish mode op layout state).memory (Arithmetic.encodeNat mode layout.target) =
      value mode op (load mode state.memory (Arithmetic.encodeNat mode layout.target)) state.accumulator state.carry := by
  rw [memory_word_effect mode op layout state ready, load_put_word]

theorem accumulator (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) :
    (finish mode op layout state).accumulator = state.accumulator := by cases mode <;> cases op <;> rfl

theorem stack (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) :
    (finish mode op layout state).stack = state.stack := by cases mode <;> cases op <;> rfl

theorem carry (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    (finish mode op layout state).carry = carryValue mode op
      (load mode state.memory (Arithmetic.encodeNat mode layout.target)) state.accumulator state.carry := by
  cases mode with
  | x86 => cases op <;> rfl
  | x64 =>
    change (executeMemory .x64 (memoryOp op) state (nextPC .x64 (form .x64 op layout) state)
      (memoryAddress .x64 (nextPC .x64 (form .x64 op layout) state) (displacement .x64 op layout))).carry = _
    rw [hits .x64 op layout state ready]
    cases op <;> rfl

theorem store_carry (mode : Mode) (layout : Layout mode) (state : State mode) :
    (finish mode .store layout state).carry = state.carry := by cases mode <;> rfl

theorem memory_frame (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state)
    (position : Nat) (outside : Not (ByteMemory.Inside layout.target mode.wordBytes position)) :
    (finish mode op layout state).memory position = state.memory position := by
  rw [memory_effect mode op layout state ready]
  exact ByteMemory.put_frame _ _ _ position (by simpa using outside)

theorem load_frame (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state)
    (observed : Word mode) (observedOwned : SpacedCombinedImage.Owned mode layout.whole layout.origin layout.gridBase observed)
    (different : Not (observed = Arithmetic.encodeNat mode layout.target)) :
    load mode (finish mode op layout state).memory observed = load mode state.memory observed := by
  rw [memory_word_effect mode op layout state ready]
  exact Writes.load_frame mode state.memory _ _ _
    (Fragment.owned_fields_separate mode layout.whole layout.origin layout.gridBase _ _ ready.gap observedOwned ready.owned different)

theorem finish_intact (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) (ready : Ready mode op layout state) :
    SpacedCombinedImage.Intact mode layout.whole layout.origin layout.gridBase (finish mode op layout state).memory :=
  SpacedCombinedImage.trace_intact mode layout.whole layout.origin layout.gridBase state _ _ ready.enough ready.gap ready.intact
    (owned_run mode op layout state ready) (trace mode op layout state ready)

theorem zero_mask (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode .subtractBorrowZero layout state)
    (zero : load mode state.memory (Arithmetic.encodeNat mode layout.target) = 0) :
    load mode (finish mode .subtractBorrowZero layout state).memory (Arithmetic.encodeNat mode layout.target) = Arithmetic.sbbZero mode state.carry := by
  rw [written_value mode .subtractBorrowZero layout state ready, zero]
  simp [value, Arithmetic.sbbZero]

theorem zero_carry (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode .subtractBorrowZero layout state)
    (zero : load mode state.memory (Arithmetic.encodeNat mode layout.target) = 0) :
    (finish mode .subtractBorrowZero layout state).carry = state.carry := by
  rw [carry mode .subtractBorrowZero layout state ready, zero]
  cases state.carry <;> simp [carryValue]

theorem program_count (mode : Mode) (op : Op) (layout : Layout mode) : (program mode op layout).length = 1 := rfl

theorem run (mode : Mode) (op : Op) (layout : Layout mode) (state : State mode) :
    runForms mode (program mode op layout) state = finish mode op layout state := rfl

end SmcTuring.Native.ScalarImage

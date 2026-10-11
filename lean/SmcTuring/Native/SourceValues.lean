module
public import SmcTuring.Native.GuardInvocationImage
public import SmcTuring.Dolan.Machine

public section

namespace SmcTuring.Native.SourceValues

open Execution

/-- The native generator uses a heap pointer for an address and 0/stride for
the two offsets. This is an encoding of the checked source's tagged words. -/
@[expose] def naturalWord (mode : Mode) (base : Nat) : Dolan.Mov.Word -> Nat
  | .address cell => Layout.heapField mode base cell false
  | .offset choice => Arithmetic.offsetValue mode choice
@[expose] def encodeWord (mode : Mode) (base : Nat) (value : Dolan.Mov.Word) : Word mode :=
  Arithmetic.encodeNat mode (naturalWord mode base value)
@[expose] def Fits (mode : Mode) (base : Nat) (value : Dolan.Mov.Word) : Prop :=
  naturalWord mode base value < 2 ^ (8 * mode.wordBytes)
@[expose] def isOffset : Dolan.Mov.Word -> Bool
  | .address _ => false
  | .offset _ => true
@[expose] def accepts (sense : GuardImage.Sense) (value : Dolan.Mov.Word) : Bool :=
  match sense with | .base => !isOffset value | .offset => isOffset value
@[expose] def AddressFits (mode : Mode) (base : Nat) (value : Dolan.Mov.Word) (choice : Bool) : Prop :=
  match value with
  | .address cell => Layout.heapField mode base cell choice < 2 ^ (8 * mode.wordBytes)
  | .offset _ => True

theorem natural_injective (mode : Mode) (base : Nat) : Function.Injective (naturalWord mode base) := by
  intro left right same
  cases left with
  | address first =>
    cases right with
    | address second =>
      have fields : Layout.fieldAddress mode base (13 + 2 * first) = Layout.fieldAddress mode base (13 + 2 * second) := same
      have indices := Layout.field_address_injective mode base fields
      have cells : first = second := by omega
      exact congrArg Dolan.Mov.Word.address cells
    | offset choice =>
      have low := Nat.lt_of_lt_of_le (Arithmetic.offset_below_boundary mode base choice)
        (Layout.heap_at_or_above_boundary mode base first false)
      change Layout.heapField mode base first false = Arithmetic.offsetValue mode choice at same
      omega
  | offset first =>
    cases right with
    | address cell =>
      have low := Nat.lt_of_lt_of_le (Arithmetic.offset_below_boundary mode base first)
        (Layout.heap_at_or_above_boundary mode base cell false)
      change Arithmetic.offsetValue mode first = Layout.heapField mode base cell false at same
      omega
    | offset second =>
      cases mode <;> cases first <;> cases second <;>
        simp_all [naturalWord, Arithmetic.offsetValue, Mode.stride, Mode.wordBytes]

theorem word_toNat (mode : Mode) (base : Nat) (value : Dolan.Mov.Word) (fits : Fits mode base value) :
    (encodeWord mode base value).toNat = naturalWord mode base value :=
  Arithmetic.encode_nat_toNat mode _ fits

theorem word_injective (mode : Mode) (base : Nat) (left right : Dolan.Mov.Word)
    (leftFits : Fits mode base left) (rightFits : Fits mode base right)
    (same : encodeWord mode base left = encodeWord mode base right) : left = right := by
  apply natural_injective mode base
  have values := congrArg (fun value : Word mode => value.toNat) same
  rw [word_toNat mode base left leftFits, word_toNat mode base right rightFits] at values
  exact values

theorem word_borrow (mode : Mode) (base : Nat) (value : Dolan.Mov.Word)
    (boundaryFits : Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes)) (fits : Fits mode base value) :
    Arithmetic.unsignedBorrow (encodeWord mode base value) (Arithmetic.encodeNat mode (Layout.heapBase mode base)) = isOffset value := by
  cases value with
  | address cell => exact Arithmetic.heap_borrow mode base cell false fits
  | offset choice => exact Arithmetic.offset_borrow mode base choice boundaryFits

/-- A wrong offset-valued base remains below the heap boundary after adding
either valid offset; in particular stride+stride cannot become an address. -/
theorem offset_sum_below_boundary (mode : Mode) (base : Nat) (first second : Bool) :
    Arithmetic.offsetValue mode first + Arithmetic.offsetValue mode second < Layout.heapBase mode base := by
  cases mode <;> cases first <;> cases second <;>
    simp [Arithmetic.offsetValue, Layout.heapBase, Layout.fieldAddress, Mode.stride, Mode.wordBytes]

theorem offset_sum_borrow (mode : Mode) (base : Nat) (first second : Bool)
    (boundaryFits : Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes)) :
    Arithmetic.unsignedBorrow (Arithmetic.encodeOffset mode first + Arithmetic.encodeOffset mode second)
      (Arithmetic.encodeNat mode (Layout.heapBase mode base)) = true := by
  have low := offset_sum_below_boundary mode base first second
  have fits := Nat.lt_trans low boundaryFits
  have sum : Arithmetic.encodeOffset mode first + Arithmetic.encodeOffset mode second =
      Arithmetic.encodeNat mode (Arithmetic.offsetValue mode first + Arithmetic.offsetValue mode second) :=
    BitVec.ofNat_add_ofNat _ _
  rw [sum, Arithmetic.borrow_encode_nat mode _ _ fits boundaryFits]
  simp [low]

theorem address_candidate_borrow (mode : Mode) (base : Nat) (value : Dolan.Mov.Word) (choice : Bool)
    (boundaryFits : Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes)) (fits : AddressFits mode base value choice) :
    Arithmetic.unsignedBorrow (encodeWord mode base value + Arithmetic.encodeOffset mode choice)
      (Arithmetic.encodeNat mode (Layout.heapBase mode base)) = isOffset value := by
  cases value with
  | address cell =>
    change Arithmetic.unsignedBorrow (Arithmetic.heapWord mode base cell false + Arithmetic.encodeOffset mode choice) _ = false
    rw [Arithmetic.indexed_heap_address]
    exact Arithmetic.heap_borrow mode base cell choice fits
  | offset first => exact offset_sum_borrow mode base first choice boundaryFits

theorem typed_guard_borrow (mode : Mode) (layout : GuardInvocationImage.Layout mode) (base : Nat)
    (state : State mode) (value : Dolan.Mov.Word)
    (candidate : load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.candidate) = encodeWord mode base value)
    (boundary : load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.boundary) = Arithmetic.encodeNat mode (Layout.heapBase mode base))
    (boundaryFits : Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes)) (fits : Fits mode base value) :
    GuardInvocationImage.borrowed mode layout state = isOffset value := by
  unfold GuardInvocationImage.borrowed GuardImage.borrowed
  rw [candidate, boundary]
  exact word_borrow mode base value boundaryFits fits

/-- The complete 89-instruction guard's branch is the source tag test, with
the actual incoming CALL end on success and the original terminal on failure. -/
theorem typed_guard_pc (mode : Mode) (layout : GuardInvocationImage.Layout mode) (base : Nat)
    (state : State mode) (value : Dolan.Mov.Word) (ready : GuardInvocationImage.Ready mode layout state)
    (candidate : load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.candidate) = encodeWord mode base value)
    (boundary : load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.boundary) = Arithmetic.encodeNat mode (Layout.heapBase mode base))
    (boundaryFits : Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes)) (fits : Fits mode base value) :
    (GuardInvocationImage.finish mode layout state).pc =
      if accepts layout.guard.sense value then GuardInvocationImage.callerEnd mode layout
      else load mode state.memory (Arithmetic.encodeNat mode layout.guard.terminal) := by
  rw [GuardInvocationImage.pc mode layout state ready, typed_guard_borrow mode layout base state value candidate boundary boundaryFits fits]
  cases layout.guard.sense <;> cases value <;> rfl

theorem address_guard_borrow (mode : Mode) (layout : GuardInvocationImage.Layout mode) (base : Nat)
    (state : State mode) (value : Dolan.Mov.Word) (choice : Bool)
    (candidate : load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.candidate) = encodeWord mode base value + Arithmetic.encodeOffset mode choice)
    (boundary : load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.boundary) = Arithmetic.encodeNat mode (Layout.heapBase mode base))
    (boundaryFits : Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes)) (fits : AddressFits mode base value choice) :
    GuardInvocationImage.borrowed mode layout state = isOffset value := by
  unfold GuardInvocationImage.borrowed GuardImage.borrowed
  rw [candidate, boundary]
  exact address_candidate_borrow mode base value choice boundaryFits fits

theorem address_guard_pc (mode : Mode) (layout : GuardInvocationImage.Layout mode) (base : Nat)
    (state : State mode) (value : Dolan.Mov.Word) (choice : Bool) (ready : GuardInvocationImage.Ready mode layout state)
    (sense : layout.guard.sense = .base)
    (candidate : load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.candidate) = encodeWord mode base value + Arithmetic.encodeOffset mode choice)
    (boundary : load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.boundary) = Arithmetic.encodeNat mode (Layout.heapBase mode base))
    (boundaryFits : Layout.heapBase mode base < 2 ^ (8 * mode.wordBytes)) (fits : AddressFits mode base value choice) :
    (GuardInvocationImage.finish mode layout state).pc =
      if accepts .base value then GuardInvocationImage.callerEnd mode layout
      else load mode state.memory (Arithmetic.encodeNat mode layout.guard.terminal) := by
  rw [GuardInvocationImage.pc mode layout state ready, sense,
    address_guard_borrow mode layout base state value choice candidate boundary boundaryFits fits]
  cases value <;> rfl

theorem source_address_encoded (mode : Mode) (base : Nat) (source : Dolan.Mov.State)
    (baseReg offsetReg : Dolan.Mov.Register) (pointer : Nat × Bool)
    (valid : Dolan.Mov.address source baseReg offsetReg = some pointer) :
    encodeWord mode base (source.registers baseReg) + encodeWord mode base (source.registers offsetReg) =
      Arithmetic.heapWord mode base pointer.1 pointer.2 := by
  cases hb : source.registers baseReg with
  | offset choice => simp [Dolan.Mov.address, hb] at valid
  | address cell =>
    cases ho : source.registers offsetReg with
    | address other => simp [Dolan.Mov.address, hb, ho] at valid
    | offset choice =>
      have same : (cell, choice) = pointer := Option.some.inj (by simpa [Dolan.Mov.address, hb, ho] using valid)
      rw [← same]
      exact Arithmetic.indexed_heap_address mode base cell choice

theorem source_address_toNat (mode : Mode) (base : Nat) (source : Dolan.Mov.State)
    (baseReg offsetReg : Dolan.Mov.Register) (pointer : Nat × Bool)
    (valid : Dolan.Mov.address source baseReg offsetReg = some pointer)
    (fits : Layout.heapField mode base pointer.1 pointer.2 < 2 ^ (8 * mode.wordBytes)) :
    (encodeWord mode base (source.registers baseReg) + encodeWord mode base (source.registers offsetReg)).toNat =
      Layout.heapField mode base pointer.1 pointer.2 := by
  rw [source_address_encoded mode base source baseReg offsetReg pointer valid]
  exact Arithmetic.encode_nat_toNat mode _ fits

end SmcTuring.Native.SourceValues

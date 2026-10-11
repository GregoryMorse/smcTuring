module
public import SmcTuring.Appendix.BranchTail
public import SmcTuring.Appendix.ByteImage

public section

namespace SmcTuring.Appendix.ByteControl

open ByteCode
abbrev State := ByteExecution.State
abbrev Word := Native.Word .x86
abbrev Memory := Native.ByteMemory.Memory

@[expose] def load (memory : Memory) (address : Word) : Word := Native.Execution.load .x86 memory address
@[expose] def put (memory : Memory) (address value : Word) : Memory := Native.ByteMemory.putWord .x86 memory address.toNat value

@[expose] def Apart (first second : Word) : Prop :=
  ∀ index : Fin 4, ¬Native.ByteMemory.Inside second.toNat 4 (first.toNat + index.val)

theorem apart_symmetric {first second : Word} (apart : Apart first second) : Apart second first := by
  intro index
  have small := index.isLt
  unfold Apart at apart
  unfold Native.ByteMemory.Inside at apart ⊢
  by_contra overlap
  have within : first.toNat ≤ second.toNat + index.val ∧ second.toNat + index.val < first.toNat + 4 := by simpa using overlap
  have below : second.toNat + index.val - first.toNat < 4 := by omega
  have outside := apart ⟨second.toNat + index.val - first.toNat, below⟩
  simp only [Nat.add_sub_of_le within.1] at outside
  omega

theorem load_put (memory : Memory) (address value : Word) : load (put memory address value) address = value :=
  Native.Execution.load_put_word .x86 memory address value

theorem load_frame (memory : Memory) (written observed value : Word) (apart : Apart observed written) :
    load (put memory written value) observed = load memory observed := Native.Writes.load_frame .x86 _ _ _ _ apart

theorem put_overwrite (memory : Memory) (address old fresh : Word) :
    put (put memory address old) address fresh = put memory address fresh := Native.Writes.put_word_overwrite .x86 _ _ _ _

theorem put_commute (memory : Memory) (first second firstValue secondValue : Word) (apart : Apart first second) :
    put (put memory first firstValue) second secondValue = put (put memory second secondValue) first firstValue :=
  Native.Writes.put_words_commute .x86 _ _ _ _ _ apart

theorem put_back (memory : Memory) (address : Word) : put memory address (load memory address) = memory :=
  Native.Writes.put_word_back .x86 _ _

@[expose] def exchangeStack (pointer : Word) (state : State) : State := ByteExecution.execute (.memory .exchangeStack pointer) state
@[expose] def exchangeAcc (pointer : Word) (state : State) : State := ByteExecution.execute (.memory .exchangeAcc pointer) state
@[expose] def addFour (pointer : Word) (state : State) : State := ByteExecution.execute (.memory .addFour pointer) state
@[expose] def storeAcc (address : Word) (state : State) : State := ByteExecution.execute (.storeAcc address) state

theorem exchange_stack_effect (pointer : Word) (state : State) : exchangeStack pointer state =
    { state with pc := BitVec.add state.pc 6, stack := load state.memory pointer, memory := put state.memory pointer state.stack } := rfl

theorem exchange_acc_effect (pointer : Word) (state : State) : exchangeAcc pointer state =
    { state with pc := BitVec.add state.pc 6, accumulator := load state.memory pointer, memory := put state.memory pointer state.accumulator } := rfl

theorem add_four_effect (pointer : Word) (state : State) : addFour pointer state =
    { state with pc := BitVec.add state.pc 7, carry := (load state.memory pointer).uaddOverflow 4, memory := put state.memory pointer (BitVec.add (load state.memory pointer) 4) } := rfl

theorem store_acc_effect (address : Word) (state : State) : storeAcc address state =
    { state with pc := BitVec.add state.pc 5, memory := put state.memory address state.accumulator } := rfl

@[expose] def restoreForms (pointer address : Word) : List Form :=
  [.memory .exchangeStack pointer, .memory .addFour pointer, .memory .exchangeAcc pointer,
    .storeAcc address, .memory .exchangeAcc pointer]
@[expose] def restore (pointer address : Word) (state : State) : State :=
  exchangeAcc pointer (storeAcc address (exchangeAcc pointer (addFour pointer (exchangeStack pointer state))))

theorem restore_run (pointer address : Word) (state : State) : ByteExecution.run (restoreForms pointer address) state = restore pointer address state := rfl

/-- Full byte-memory restoration effect for arbitrary incoming state. No
successful CALL or future fetch trace is assumed. The final five stores are real. -/
theorem restore_effect (pointer address : Word) (state : State) (apart : Apart pointer address) :
    restore pointer address state =
      { pc := BitVec.add state.pc 30
        accumulator := state.accumulator
        stack := load state.memory pointer
        carry := state.stack.uaddOverflow 4
        memory := put (put state.memory pointer (BitVec.add state.stack 4)) address (BitVec.add state.stack 4) } := by
  simp only [restore, exchange_stack_effect, add_four_effect, exchange_acc_effect, store_acc_effect,
    load_put, put_overwrite, load_frame _ address pointer _ apart]
  rw [put_commute _ address pointer _ _ (apart_symmetric apart), put_overwrite]
  congr 1
  change (((((state.pc + (6 : Word)) + 7) + 6) + 5) + 6) = state.pc + (30 : Word)
  simp only [BitVec.add_assoc]
  rfl

theorem call_effect (displacement : Word) (state : State) :
    ByteExecution.execute (.callRelative displacement) state =
      { state with pc := BitVec.add (BitVec.add state.pc 5) displacement, stack := BitVec.sub state.stack 4, memory := put state.memory (BitVec.sub state.stack 4) (BitVec.add state.pc 5) } := rfl

@[expose] def tailForms (pointer displacement : Word) (state : State) : List Form :=
  [.memory .exchangeStack pointer, .callRelative (load (exchangeStack pointer state).memory displacement)]
@[expose] def tail (pointer displacement : Word) (state : State) : State :=
  ByteExecution.execute (.callRelative (load (exchangeStack pointer state).memory displacement)) (exchangeStack pointer state)

theorem tail_run (pointer displacement : Word) (state : State) : ByteExecution.run (tailForms pointer displacement state) state = tail pointer displacement state := rfl

/-- The displacement is actually read after XCHG ESP. The write at CALL's
slot cannot retroactively change the already evaluated transfer target. -/
theorem tail_effect (pointer displacement : Word) (state : State) (apart : Apart displacement pointer) :
    tail pointer displacement state =
      { pc := BitVec.add (BitVec.add state.pc 11) (load state.memory displacement)
        accumulator := state.accumulator
        stack := BitVec.sub (load state.memory pointer) 4
        carry := state.carry
        memory := put (put state.memory pointer state.stack) (BitVec.sub (load state.memory pointer) 4)
          (BitVec.add state.pc 11) } := by
  have sum : BitVec.add (BitVec.add state.pc 6) 5 = BitVec.add state.pc 11 := by
    change (state.pc + (6 : Word)) + 5 = state.pc + (11 : Word)
    rw [BitVec.add_assoc]
    rfl
  simp only [tail, exchange_stack_effect, call_effect, load_frame _ pointer displacement _ apart, sum]

/-- The exact DEFSTACK alias restores the ENTIRE byte memory, including
unchanged/unaligned bytes and the temporary return/address word. -/
theorem continued_alias (pointer displacement address : Word) (state : State)
    (callApart : Apart displacement pointer) (slotApart : Apart pointer address)
    (top : load state.memory pointer = pointer) (slotAlias : BitVec.sub pointer 4 = address)
    (addressValue : load state.memory address = pointer) (nonwrap : 4 ≤ pointer.toNat) :
    restore pointer address (tail pointer displacement state) =
      { state with pc := BitVec.add (tail pointer displacement state).pc 30, carry := false } := by
  rw [restore_effect pointer address _ slotApart, tail_effect pointer displacement state callApart, top, slotAlias]
  have repaired : BitVec.add address 4 = pointer := by rw [←slotAlias]; exact BitVec.sub_add_cancel _ _
  change ({ pc := BitVec.add (BitVec.add (BitVec.add state.pc 11) (load state.memory displacement)) 30
            accumulator := state.accumulator
            stack := load (put (put state.memory pointer state.stack) address (BitVec.add state.pc 11)) pointer
            carry := address.uaddOverflow 4
            memory := put (put (put (put state.memory pointer state.stack) address (BitVec.add state.pc 11)) pointer (BitVec.add address 4)) address (BitVec.add address 4) } : State) =
    { state with pc := BitVec.add (BitVec.add (BitVec.add state.pc 11) (load state.memory displacement)) 30, carry := false }
  rw [repaired, load_frame _ address pointer _ slotApart, load_put]
  have memory : put (put (put (put state.memory pointer state.stack) address (BitVec.add state.pc 11)) pointer pointer) address pointer = state.memory := by
    have pointerBack : put state.memory pointer pointer = state.memory := by
      simpa only [top] using put_back state.memory pointer
    have addressBack : put state.memory address pointer = state.memory := by
      simpa only [addressValue] using put_back state.memory address
    rw [put_commute _ address pointer _ _ (apart_symmetric slotApart), put_overwrite,
      put_overwrite, pointerBack, addressBack]
  rw [memory]
  have carry : address.uaddOverflow 4 = false := by
    rw [←slotAlias]
    exact BranchTail.slot_add_no_carry pointer nonwrap
  rw [carry]

end SmcTuring.Appendix.ByteControl

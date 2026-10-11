module
public import SmcTuring.Appendix.Branching

public section

namespace SmcTuring.Appendix.BranchTail

open Machine32

/-- The observed field-word state, with x86 ESP and the near-CALL IP.
This is not a byte-layout or full-CPU refinement. -/
structure State where
  data : Machine32.State
  stack : Word
  pc : Word

/-- The printed x86 absolute-memory XCHG ESP is six bytes in the selected
ModR/M form. Its write is real even when the exchanged values are equal. -/
@[expose] def exchangeStack (pointer : Nat) (state : State) : State :=
  { state with
      data := put state.data pointer state.stack state.data.carry
      stack := state.data.memory pointer
      pc := state.pc + 6 }

/-- The E8 CALL target is sampled from the current displacement field before
its return write. Modular ESP arithmetic is explicit; allocation is separate. -/
@[expose] def call (displacement : Word) (state : State) : State :=
  let next := state.pc + 5
  let slot := state.stack - 4
  { state with
      data := put state.data slot.toNat next state.data.carry
      stack := slot
      pc := next + displacement }

@[expose] def tail (pointer displacement : Nat) (state : State) : State :=
  let exchanged := exchangeStack pointer state
  call (exchanged.data.memory displacement) exchanged

@[expose] def next (state : State) : Word := (state.pc + 6) + 5
@[expose] def slot (pointer : Nat) (state : State) : Word := state.data.memory pointer - 4

/-- The complete actual single-exchange/CALL effect, without a future trace
or a preselected branch result. The displacement is read after the exchange. -/
theorem tail_effect (pointer displacement : Nat) (state : State)
    (separate : displacement ≠ pointer) :
    tail pointer displacement state =
      { data := { state.data with
          memory := write (write state.data.memory pointer state.stack)
            (slot pointer state).toNat (next state) }
        stack := slot pointer state
        pc := next state + state.data.memory displacement } := by
  simp [tail, exchangeStack, call, put, write, slot, next, separate]

theorem tail_pc (pointer displacement : Nat) (state : State)
    (separate : displacement ≠ pointer) :
    (tail pointer displacement state).pc = next state + state.data.memory displacement := by
  rw [tail_effect pointer displacement state separate]

theorem tail_stack (pointer displacement : Nat) (state : State) :
    (tail pointer displacement state).stack = slot pointer state := rfl

theorem tail_accumulator (pointer displacement : Nat) (state : State) :
    (tail pointer displacement state).data.accumulator = state.data.accumulator := rfl

theorem tail_carry (pointer displacement : Nat) (state : State) :
    (tail pointer displacement state).data.carry = state.data.carry := rfl

theorem tail_return (pointer displacement : Nat) (state : State) :
    (tail pointer displacement state).data.memory (slot pointer state).toNat = next state := by
  simp [tail, call, exchangeStack, slot, next, put, write]

theorem tail_frame (pointer displacement : Nat) (state : State) (field : Nat)
    (notPointer : field ≠ pointer) (notSlot : field ≠ (slot pointer state).toNat) :
    (tail pointer displacement state).data.memory field = state.data.memory field := by
  change (write (write state.data.memory pointer state.stack)
    (slot pointer state).toNat (next state)) field = state.data.memory field
  simp only [write, notSlot, notPointer, ite_false]

/-- The two actual writes: the saved incoming ESP at the pointer immediate
and the CALL's complete return IP at the code-backed slot. -/
@[expose] def TailPure (codeField : Nat → Prop) (pointer : Nat) (state : State) : Prop :=
  codeField pointer ∧ codeField (slot pointer state).toNat

theorem tail_pure (codeField : Nat → Prop) (pointer : Nat) (state : State)
    (pointerOwned : codeField pointer) (slotOwned : codeField (slot pointer state).toNat) :
    TailPure codeField pointer state := ⟨pointerOwned, slotOwned⟩

/-- JUMPTARGET's observed register/word projection excludes its instruction
pointer. Its exact byte lengths/current fetch remain the emitter obligation. -/
structure Registers where
  data : Machine32.State
  stack : Word

/-- Five printed instructions, in order: XCHG ESP,pointer; ADD pointer,4;
XCHG EAX,pointer; MOV address,EAX; XCHG EAX,pointer. The MOV consumes the
actual accumulator produced by the preceding exchange. -/
@[expose] def restore (pointer address : Nat) (state : State) : Registers :=
  let exchanged := exchangeStack pointer state
  let added := put exchanged.data pointer (exchanged.data.memory pointer + 4)
    ((exchanged.data.memory pointer).uaddOverflow 4)
  let loaded := execute (.exchange pointer) added
  let stored := execute (.store address loaded.accumulator) loaded
  let restored := execute (.exchange pointer) stored
  ⟨restored, exchanged.stack⟩

/-- The restoration effect holds for arbitrary incoming values. In particular
there is no assumption here that the CALL has already succeeded. -/
theorem restore_effect (pointer address : Nat) (state : State)
    (separate : address ≠ pointer) :
    restore pointer address state =
      { data := { state.data with
          carry := state.stack.uaddOverflow 4,
          memory := write (write state.data.memory pointer (state.stack + 4))
            address (state.stack + 4) },
        stack := state.data.memory pointer } := by
  unfold restore
  simp only [exchangeStack, execute, put]
  congr 1
  · congr 1
    · simp [write, Ne.symm separate]
    · simp [write]
    · funext field
      by_cases p : field = pointer
      · subst field
        simp [write, Ne.symm separate]
      · by_cases a : field = address
        · subst field
          simp [write, separate]
        · simp [write, p, a]

theorem restore_accumulator (pointer address : Nat) (state : State)
    (separate : address ≠ pointer) :
    (restore pointer address state).data.accumulator = state.data.accumulator := by
  rw [restore_effect pointer address state separate]

theorem restore_frame (pointer address : Nat) (state : State) (field : Nat)
    (separate : address ≠ pointer) (notPointer : field ≠ pointer)
    (notAddress : field ≠ address) :
    (restore pointer address state).data.memory field = state.data.memory field := by
  rw [restore_effect pointer address state separate]
  simp [write, notPointer, notAddress]

/-- Actual intermediate destinations of the five restoration writes. -/
@[expose] def restorationWrites (pointer address : Nat) : List Nat :=
  [pointer, pointer, pointer, address, pointer]

theorem restoration_count (pointer address : Nat) :
    (restorationWrites pointer address).length = 5 := rfl

theorem restoration_pure (codeField : Nat → Prop) (pointer address : Nat)
    (pointerOwned : codeField pointer) (addressOwned : codeField address) :
    ∀ field ∈ restorationWrites pointer address, codeField field := by
  simp_all [restorationWrites]

/-- Return continuation restores the original ESP and pointer value. The address
field receives the restored top. This allows the printed slot/address alias;
a return word persists only in the separately stated disjoint-slot case. -/
theorem continued_effect (pointer displacement address : Nat) (state : State)
    (callSeparate : displacement ≠ pointer) (addressSeparate : address ≠ pointer)
    (slotSeparate : (slot pointer state).toNat ≠ pointer) :
    restore pointer address (tail pointer displacement state) =
      { data := { state.data with
          carry := (slot pointer state).uaddOverflow 4,
          memory := write (write state.data.memory (slot pointer state).toNat (next state))
            address (state.data.memory pointer) },
        stack := state.stack } := by
  rw [restore_effect pointer address _ addressSeparate,
    tail_effect pointer displacement state callSeparate]
  have top : slot pointer state + 4 = state.data.memory pointer := by
    simp [slot,BitVec.sub_add_cancel]
  simp only [top]
  congr 1
  · congr 1
    funext field
    by_cases a : field = address
    · subst field
      simp [write]
    · by_cases p : field = pointer
      · subst field
        simp [write, a, Ne.symm slotSeparate]
      · simp [write, a, p]
  · simp [write, Ne.symm slotSeparate]

theorem continued_return (pointer displacement address : Nat) (state : State)
    (callSeparate : displacement ≠ pointer) (addressSeparate : address ≠ pointer)
    (slotSeparate : (slot pointer state).toNat ≠ pointer)
    (slotAddress : (slot pointer state).toNat ≠ address) :
    (restore pointer address (tail pointer displacement state)).data.memory
      (slot pointer state).toNat = next state := by
  rw [continued_effect pointer displacement address state callSeparate addressSeparate slotSeparate]
  simp [write, slotAddress]

theorem continued_frame (pointer displacement address : Nat) (state : State) (field : Nat)
    (callSeparate : displacement ≠ pointer) (addressSeparate : address ≠ pointer)
    (slotSeparate : (slot pointer state).toNat ≠ pointer)
    (notSlot : field ≠ (slot pointer state).toNat) (notAddress : field ≠ address) :
    (restore pointer address (tail pointer displacement state)).data.memory field =
      state.data.memory field := by
  rw [continued_effect pointer displacement address state callSeparate addressSeparate slotSeparate]
  simp [write, notSlot, notAddress]

/-- The literal DEFSTACK has CALL's return slot equal to the defining MOV's
address operand. JUMPTARGET consumes this alias and restores the whole memory;
the temporary return word is intentionally replaced by the old top. -/
theorem continued_alias (pointer displacement address : Nat) (state : State)
    (callSeparate : displacement ≠ pointer) (addressSeparate : address ≠ pointer)
    (slotAddress : (slot pointer state).toNat = address)
    (addressValue : state.data.memory address = state.data.memory pointer) :
    restore pointer address (tail pointer displacement state) =
      { data := { state.data with carry := (slot pointer state).uaddOverflow 4 },
        stack := state.stack } := by
  have slotSeparate : (slot pointer state).toNat ≠ pointer := by
    simpa [slotAddress] using addressSeparate
  rw [continued_effect pointer displacement address state callSeparate addressSeparate slotSeparate]
  have memory : write (write state.data.memory (slot pointer state).toNat (next state))
      address (state.data.memory pointer) = state.data.memory := by
    funext field
    by_cases same : field = address
    · subst field
      simp [write, addressValue]
    · simp [write, slotAddress, same]
  rw [memory]

/-- A nonwrapping pointer top gives no CF on the continuation's ADD slot,4.
The literal address layout must separately establish this resource condition. -/
theorem slot_add_no_carry (top : Word) (nonwrap : 4 ≤ top.toNat) :
    (top - 4).uaddOverflow 4 = false := by
  have noBorrow : ¬ top.usubOverflow 4 := by
    simpa [BitVec.usubOverflow] using nonwrap
  have value : (top - 4).toNat = top.toNat - 4 :=
    BitVec.toNat_sub_of_not_usubOverflow noBorrow
  have bound := top.isLt
  simp only [BitVec.uaddOverflow, value]
  norm_num
  omega

theorem continued_alias_no_carry (pointer displacement address : Nat) (state : State)
    (callSeparate : displacement ≠ pointer) (addressSeparate : address ≠ pointer)
    (slotAddress : (slot pointer state).toNat = address)
    (addressValue : state.data.memory address = state.data.memory pointer)
    (nonwrap : 4 ≤ (state.data.memory pointer).toNat) :
    restore pointer address (tail pointer displacement state) =
      { data := { state.data with carry := false }, stack := state.stack } := by
  rw [continued_alias pointer displacement address state callSeparate addressSeparate slotAddress addressValue]
  simp only [slot, slot_add_no_carry _ nonwrap]

/-- The branch-prefix field effect lifted at its tail boundary. Its PC is the
XCHG entry address supplied by a future byte layout, not a claimed prefix length. -/
@[expose] def prefixed (fields : Branching.Fields) (signed : Bool)
    (relation : BranchAlgebra.Relation) (delta : Word) (state : State) : State :=
  { state with data := run (Branching.relationProgram fields signed relation delta) state.data }

@[expose] def branch (fields : Branching.Fields) (signed : Bool)
    (relation : BranchAlgebra.Relation) (target : Word) (pointer : Nat) (state : State) : State :=
  tail pointer fields.displacement
    (prefixed fields signed relation (target - next state) state)

theorem prefixed_frame (fields : Branching.Fields) (signed : Bool)
    (relation : BranchAlgebra.Relation) (delta : Word) (state : State)
    (separate : Branching.Separate fields) (field : Nat)
    (outside : field ∉ [fields.mask, fields.displacement, fields.delta]) :
    (prefixed fields signed relation delta state).data.memory field = state.data.memory field :=
  Branching.relation_frame fields signed relation delta state.data separate field outside

/-- Both chosen branch endpoints follow from the actual prefix followed by the
literal XCHG/CALL, not from a supplied selected displacement. -/
theorem branch_pc (fields : Branching.Fields) (signed : Bool)
    (relation : BranchAlgebra.Relation) (target : Word) (pointer : Nat) (state : State)
    (separate : Branching.Separate fields) (callSeparate : fields.displacement ≠ pointer) :
    (branch fields signed relation target pointer state).pc =
      if BranchAlgebra.holds signed relation (state.data.memory fields.x) (state.data.memory fields.y)
      then target else next state := by
  unfold branch
  rw [tail_pc pointer fields.displacement _ callSeparate]
  exact Branching.relation_target fields signed relation (next state) target state.data separate

/-- Literal code-backed stack reuse composes with every proved branch relation.
The prefix's scratch effects remain, the original ESP/accumulator and all its
boundary words are restored, and CF is false. No continuation IP/fetch is claimed. -/
theorem branch_restored (fields : Branching.Fields) (signed : Bool)
    (relation : BranchAlgebra.Relation) (target : Word) (pointer address : Nat) (state : State)
    (separate : Branching.Separate fields) (callSeparate : fields.displacement ≠ pointer)
    (addressSeparate : address ≠ pointer)
    (pointerOutside : pointer ∉ [fields.mask, fields.displacement, fields.delta])
    (addressOutside : address ∉ [fields.mask, fields.displacement, fields.delta])
    (slotAddress : (slot pointer state).toNat = address)
    (addressValue : state.data.memory address = state.data.memory pointer)
    (nonwrap : 4 ≤ (state.data.memory pointer).toNat) :
    restore pointer address (branch fields signed relation target pointer state) =
      { data := (prefixed fields signed relation (target - next state) state).data,
        stack := state.stack } := by
  have p := prefixed_frame fields signed relation (target - next state) state separate pointer pointerOutside
  have a := prefixed_frame fields signed relation (target - next state) state separate address addressOutside
  have restored := continued_alias_no_carry pointer fields.displacement address
    (prefixed fields signed relation (target - next state) state) callSeparate addressSeparate
    (by simpa only [slot, p] using slotAddress)
    (by simpa only [a, p] using addressValue)
    (by simpa only [p] using nonwrap)
  rw [branch, restored]
  have cf := Branching.relation_carry fields signed relation (target - next state) state.data
  simp only [prefixed]
  cases result : run (Branching.relationProgram fields signed relation (target - next state)) state.data with
  | mk acc carry memory =>
    simp only [result] at cf ⊢
    simp only [cf]

/-- Prefix, two tail writes and five restoration writes are all owned at their
actual destinations. Proving these are byte fields of live instructions is E05. -/
theorem branch_pure (codeField : Nat → Prop) (fields : Branching.Fields) (signed : Bool)
    (relation : BranchAlgebra.Relation) (target : Word) (pointer address : Nat) (state : State)
    (separate : Branching.Separate fields)
    (pointerOutside : pointer ∉ [fields.mask, fields.displacement, fields.delta])
    (owned : ∀ field ∈ [fields.x, fields.y, fields.mask, fields.displacement, fields.delta], codeField field)
    (pointerOwned : codeField pointer) (addressOwned : codeField address)
    (slotOwned : codeField (slot pointer state).toNat) :
    PureRun codeField (Branching.relationProgram fields signed relation (target - next state)) state.data ∧
      TailPure codeField pointer (prefixed fields signed relation (target - next state) state) ∧
      (∀ field ∈ restorationWrites pointer address, codeField field) := by
  have p := prefixed_frame fields signed relation (target - next state) state separate pointer pointerOutside
  exact ⟨Branching.relation_pure codeField fields signed relation (target - next state) state.data owned,
    tail_pure codeField pointer _ pointerOwned (by simpa only [slot, p] using slotOwned),
    restoration_pure codeField pointer address pointerOwned addressOwned⟩

end SmcTuring.Appendix.BranchTail

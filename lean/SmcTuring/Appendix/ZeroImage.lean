module
public import SmcTuring.Appendix.BytePacking

public section
namespace SmcTuring.Appendix.ZeroImage
open ByteImage
open ByteCode (Form fetch)
abbrev State := ByteExecution.State

/-- Listing 6: force the full DWORD immediate once at assembly time;
later clearing it does not re-assemble or shorten the protected packet. -/
@[expose] def owner (start : Nat) (initial : Word) : Entry :=
  ⟨start, .immediate .bitXor (FieldRefinement.address (start + 6)) initial⟩
@[expose] def whole (start : Nat) (initial : Word) : List Entry := [owner start initial]
@[expose] def form (start : Nat) (native : State) : Form :=
  .immediate .bitXor (FieldRefinement.address (start + 6)) (wordAt native.memory (start + 6))
@[expose] def finish (start : Nat) (native : State) : State := ByteExecution.execute (form start native) native
@[expose] def reenter (start : Nat) (native : State) : State := { native with pc := FieldRefinement.address start }

theorem packet_length (start : Nat) (initial : Word) : (owner start initial).bytes.length = 10 := rfl

theorem field_owned (start : Nat) (initial : Word) : Owned (whole start initial) (start + 6) := by
  refine ⟨owner start initial, List.mem_singleton_self _, ?_⟩
  exact List.mem_singleton_self _

theorem separated (start : Nat) (initial : Word) : Separated (whole start initial) := by
  intro first firstMember second secondMember different
  have firstEq : first = owner start initial := List.mem_singleton.mp firstMember
  have secondEq : second = owner start initial := List.mem_singleton.mp secondMember
  exact False.elim (different (firstEq.trans secondEq.symm))

theorem initial_intact (start : Nat) (initial : Word) (backing : Memory) :
    Intact (whole start initial) (image (whole start initial) backing) :=
  initialized_intact _ _ (separated start initial)

theorem current_form (start : Nat) (initial : Word) (native : State) :
    current (owner start initial) native.memory = form start native := rfl

/-- Both operands of the live XOR are the same complete word. -/
theorem current_value (start : Nat) (native : State) (fits : start + 10 ≤ 2 ^ 32) :
    ByteExecution.value (form start native) native = 0 := by
  have fieldFits : start + 6 + 4 ≤ 2 ^ 32 := by omega
  change ByteExecution.prior native (FieldRefinement.address (start + 6)) ^^^ wordAt native.memory (start + 6) = 0
  rw [word_at_read_field native _ fieldFits]
  exact BitVec.xor_self

theorem fetched (start : Nat) (initial : Word) (native : State) (fits : start + 10 ≤ 2 ^ 32)
    (intact : Intact (whole start initial) native.memory)
    (entry : native.pc = FieldRefinement.address start) : fetch native.memory native.pc.toNat = some (form start native) := by
  rw [entry]
  change fetch native.memory (FieldRefinement.address start).toNat = some (form start native)
  rw [FieldRefinement.address_toNat start (by omega), ←current_form start initial native]
  exact fetch_current _ _ (intact _ (List.mem_singleton_self _))

theorem step_correct (start : Nat) (initial : Word) (native : State) (fits : start + 10 ≤ 2 ^ 32)
    (intact : Intact (whole start initial) native.memory) (entry : native.pc = FieldRefinement.address start) :
    ByteExecution.step native = some (finish start native) := by
  simp only [ByteExecution.step, fetched start initial native fits intact entry, Option.map_some]
  rfl

theorem effect (start : Nat) (native : State) (fits : start + 10 ≤ 2 ^ 32)
    (entry : native.pc = FieldRefinement.address start) :
    finish start native =
      { pc := FieldRefinement.address (start + 10), accumulator := native.accumulator,
        stack := native.stack, carry := false, memory := Native.ByteMemory.putWord .x86 native.memory (start + 6) 0 } := by
  rw [finish, ByteExecution.execute_effect]
  have zero := current_value start native fits
  have dest : (ByteExecution.destination (form start native) native).toNat = start + 6 :=
    FieldRefinement.address_toNat _ (by omega)
  rw [zero, dest]
  have endpoint : ByteExecution.pc (form start native) native = FieldRefinement.address (start + 10) := by
    change BitVec.add native.pc (BitVec.ofNat 32 10) = FieldRefinement.address (start + 10)
    rw [entry]
    exact BitVec.ofNat_add_ofNat _ _
  rw [endpoint]
  rfl

theorem written_zero (start : Nat) (native : State) (fits : start + 10 ≤ 2 ^ 32) :
    FieldRefinement.readField (finish start native) (start + 6) = 0 := by
  have word := ByteExecution.written_word (form start native) native
  change FieldRefinement.readField (finish start native) (start + 6) = ByteExecution.value (form start native) native at word
  rw [current_value start native fits] at word
  exact word

theorem intact_after (start : Nat) (initial : Word) (native : State) (fits : start + 10 ≤ 2 ^ 32)
    (intact : Intact (whole start initial) native.memory) : Intact (whole start initial) (finish start native).memory := by
  apply execute_intact _ _ _ (separated start initial) intact
  change Owned (whole start initial) (FieldRefinement.address (start + 6)).toNat
  rw [FieldRefinement.address_toNat _ (by omega)]
  exact field_owned start initial

theorem frame (start : Nat) (native : State) (fits : start + 10 ≤ 2 ^ 32) (position : Nat)
    (outside : ¬Native.ByteMemory.Inside (start + 6) 4 position) :
    (finish start native).memory position = native.memory position := by
  apply ByteExecution.execute_frame
  change ¬Native.ByteMemory.Inside (FieldRefinement.address (start + 6)).toNat 4 position
  rwa [FieldRefinement.address_toNat _ (by omega)]

theorem trace (start : Nat) (initial : Word) (native : State) (fits : start + 10 ≤ 2 ^ 32)
    (intact : Intact (whole start initial) native.memory) (entry : native.pc = FieldRefinement.address start) :
    ByteExecution.Trace native [form start native] (finish start native) :=
  .step (fetched start initial native fits intact entry) (.nil _)

theorem owned_run (start : Nat) (initial : Word) (native : State) (fits : start + 10 ≤ 2 ^ 32) :
    ByteExecution.OwnedRun (fun word => Owned (whole start initial) word.toNat) [form start native] native := by
  change Owned (whole start initial) (FieldRefinement.address (start + 6)).toNat ∧ True
  rw [FieldRefinement.address_toNat _ (by omega)]
  exact ⟨field_owned start initial, trivial⟩

/-- Full corrected literal-byte contract for every live DWORD, register state
and backing byte. Only intact initial bytes, entry and extent are supplied. -/
theorem correct (start : Nat) (initial : Word) (native : State) (fits : start + 10 ≤ 2 ^ 32)
    (intact : Intact (whole start initial) native.memory) (entry : native.pc = FieldRefinement.address start) :
    ByteExecution.Trace native [form start native] (finish start native) ∧
    FieldRefinement.readField (finish start native) (start + 6) = 0 ∧
    (finish start native).accumulator = native.accumulator ∧
    (finish start native).stack = native.stack ∧
    (finish start native).carry = false ∧
    (finish start native).pc = FieldRefinement.address (start + 10) ∧
    ByteExecution.OwnedRun (fun word => Owned (whole start initial) word.toNat) [form start native] native ∧
    Intact (whole start initial) (finish start native).memory ∧
    forall position, ¬Native.ByteMemory.Inside (start + 6) 4 position ->
      (finish start native).memory position = native.memory position := by
  have effects := effect start native fits entry
  refine ⟨trace start initial native fits intact entry, written_zero start native fits,
    ?_, ?_, ?_, ?_, owned_run start initial native fits, intact_after start initial native fits intact,
    frame start native fits⟩ <;> rw [effects]

theorem original_image_correct (start : Nat) (initial : Word) (backing : Memory) (native : State)
    (fits : start + 10 ≤ 2 ^ 32) (initialized : native.memory = image (whole start initial) backing)
    (entry : native.pc = FieldRefinement.address start) :
    ByteExecution.Trace native [form start native] (finish start native) ∧
    FieldRefinement.readField (finish start native) (start + 6) = 0 ∧
    (finish start native).accumulator = native.accumulator ∧
    (finish start native).stack = native.stack ∧
    (finish start native).carry = false ∧
    Intact (whole start initial) (finish start native).memory := by
  have intact : Intact (whole start initial) native.memory := by rw [initialized]; exact initial_intact _ _ _
  rcases correct start initial native fits intact entry with ⟨trace, zero, acc, stack, carry, _, _, intact, _⟩
  exact ⟨trace, zero, acc, stack, carry, intact⟩

theorem reentry_intact (start : Nat) (initial : Word) (native : State) (fits : start + 10 ≤ 2 ^ 32)
    (intact : Intact (whole start initial) native.memory) :
    Intact (whole start initial) (reenter start (finish start native)).memory := intact_after start initial native fits intact

theorem reentry_trace (start : Nat) (initial : Word) (native : State) (fits : start + 10 ≤ 2 ^ 32)
    (intact : Intact (whole start initial) native.memory) :
    ByteExecution.Trace (reenter start (finish start native))
      [form start (reenter start (finish start native))] (finish start (reenter start (finish start native))) :=
  trace start initial _ fits (reentry_intact start initial native fits intact) rfl

end SmcTuring.Appendix.ZeroImage

module
public import SmcTuring.Native.MemoryRegion

public section

namespace SmcTuring.Native.RegionExecution

open Execution MemoryRegion

/-- Selected forms have at most one data read. Indirect CALL reads its target
before its distinct decremented-SP write; ordinary stores do not read their destination. -/
@[expose] def readAddress (mode : Mode) (form : Form mode) (state : State mode) : Option (Word mode) :=
  match form with
  | .exchangeIndirect => some state.accumulator
  | .memory .storeAcc _ | .memory .storeStack _ => none
  | .memory _ displacement => some (memoryAddress mode (nextPC mode form state) displacement)
  | _ => none

@[expose] def ReadWithin (mode : Mode) (region : Region) (form : Form mode) (state : State mode) : Prop :=
  match readAddress mode form state with
  | none => True
  | some address => region.Contains address.toNat mode.wordBytes

instance (mode : Mode) (region : Region) (form : Form mode) (state : State mode) :
    Decidable (ReadWithin mode region form state) := by
  unfold ReadWithin
  cases readAddress mode form state <;> infer_instance

@[expose] def StateAgree (mode : Mode) (region : Region) (left right : State mode) : Prop :=
  left.pc = right.pc ∧ left.accumulator = right.accumulator ∧ left.stack = right.stack ∧
    left.carry = right.carry ∧ Agree region left.memory right.memory

theorem state_agree_refl (mode : Mode) (region : Region) (state : State mode) :
    StateAgree mode region state state := ⟨rfl, rfl, rfl, rfl, agree_refl region _⟩

/-- Identical loaded bytes suffice for the complete selected ISA effect.
No equality or contents are required for memory outside the finite interval. -/
theorem execute_agrees (mode : Mode) (region : Region) (form : Form mode)
    (left right : State mode) (same : StateAgree mode region left right)
    (reads : ReadWithin mode region form right) :
    StateAgree mode region (execute mode form left) (execute mode form right) := by
  rcases left with ⟨leftPC, leftAcc, leftSP, leftCF, leftMemory⟩
  rcases right with ⟨rightPC, rightAcc, rightSP, rightCF, rightMemory⟩
  rcases same with ⟨samePC, sameAcc, sameSP, sameCF, memory⟩
  dsimp at samePC sameAcc sameSP sameCF
  subst rightPC; subst rightAcc; subst rightSP; subst rightCF
  cases form with
  | moffs address =>
    exact ⟨rfl, rfl, rfl, rfl, put_word_agree mode region memory _ _⟩
  | callRelative displacement =>
    exact ⟨rfl, rfl, rfl, rfl, put_word_agree mode region memory _ _⟩
  | exchangeIndirect =>
    have loaded := load_agree mode region memory leftAcc reads
    exact ⟨rfl, loaded, rfl, rfl, put_word_agree mode region memory _ _⟩
  | memory operation displacement =>
    cases operation <;> simp only [ReadWithin, readAddress, nextPC] at reads
    all_goals simp only [StateAgree, execute, executeMemory, storeState, callState, nextPC]
    all_goals try (have loaded := load_agree mode region memory _ reads; simp only [loaded])
    all_goals simp only [true_and]
    all_goals first
      | exact put_word_agree mode region memory _ _
      | exact ⟨rfl, put_word_agree mode region memory _ _⟩

/-- The actual destination also agrees, including CALL's stack slot. -/
theorem write_address_agrees (mode : Mode) (region : Region) (form : Form mode)
    (left right : State mode) (same : StateAgree mode region left right) :
    Writes.address mode form left = Writes.address mode form right := by
  cases form with
  | moffs address => rfl
  | exchangeIndirect => exact same.2.1
  | callRelative displacement => simp only [Writes.address, same.2.2.1]
  | memory operation displacement =>
    cases operation <;> simp only [Writes.address, nextPC, same.1, same.2.2.1]

/-- The value of each complete word write depends only on contained data reads. -/
theorem write_value_agrees (mode : Mode) (region : Region) (form : Form mode)
    (left right : State mode) (same : StateAgree mode region left right)
    (reads : ReadWithin mode region form right) :
    Writes.value mode form left = Writes.value mode form right := by
  have next : nextPC mode form left = nextPC mode form right := by simp only [nextPC, same.1]
  cases form with
  | moffs address => exact same.2.1
  | exchangeIndirect => exact same.2.1
  | callRelative displacement => exact next
  | memory operation displacement =>
    cases operation <;> simp only [ReadWithin, readAddress] at reads
    all_goals try have loaded := load_agree mode region same.2.2.2.2 _ reads
    all_goals simp only [Writes.value, nextPC, same.1, same.2.1, same.2.2.1, same.2.2.2.1]
    all_goals try exact congrArg (fun prior => prior + right.accumulator) loaded
    all_goals try exact congrArg (fun prior => prior - right.accumulator) loaded
    all_goals try exact congrArg (fun prior => prior ^^^ right.accumulator) loaded
    all_goals try exact congrArg (fun prior => prior &&& right.accumulator) loaded
    all_goals try exact congrArg (fun prior => prior - (if right.carry then 1 else 0)) loaded

/-- Fetch's actual classifier is used. The three-byte header and the exact
classifier-selected packet must both be contained; no external form or length oracle. -/
@[expose] def FetchWithin (mode : Mode) (region : Region) (state : State mode) : Prop :=
  region.Contains state.pc.toNat 3 ∧
    match Fetch.lengthOfBytes mode (ByteMemory.bytesAt state.memory state.pc.toNat 3) with
    | none => True
    | some count => region.Contains state.pc.toNat count

instance (mode : Mode) (region : Region) (state : State mode) : Decidable (FetchWithin mode region state) := by
  unfold FetchWithin
  cases Fetch.lengthOfBytes mode (ByteMemory.bytesAt state.memory state.pc.toNat 3) <;> infer_instance

/-- Automatic current-byte fetch is independent of every exterior completion,
including when the selected decoder rejects the instruction. -/
theorem fetch_agrees (mode : Mode) (region : Region) (left right : State mode)
    (same : StateAgree mode region left right) (contained : FetchWithin mode region right) :
    Fetch.fetch mode left.memory left.pc.toNat = Fetch.fetch mode right.memory right.pc.toNat := by
  have header := bytes_agree region same.2.2.2.2 right.pc.toNat 3 contained.1
  simp only [Fetch.fetch, same.1, header]
  cases length : Fetch.lengthOfBytes mode (ByteMemory.bytesAt right.memory right.pc.toNat 3) with
  | none => rfl
  | some count =>
    have packet : region.Contains right.pc.toNat count := by
      simpa only [FetchWithin, length] using contained.2
    simp only [Option.bind_some]
    rw [bytes_agree region same.2.2.2.2 right.pc.toNat count packet]

/-- A model step's full finite access footprint. Instruction bytes and data reads
are distinct from its complete word-write destination. -/
@[expose] def Safe (mode : Mode) (region : Region) (form : Form mode) (state : State mode) : Prop :=
  FetchWithin mode region state ∧ ReadWithin mode region form state ∧
    region.Contains (Writes.address mode form state).toNat mode.wordBytes

instance (mode : Mode) (region : Region) (form : Form mode) (state : State mode) :
    Decidable (Safe mode region form state) := by unfold Safe; infer_instance


theorem state_agree_symm (mode : Mode) (region : Region) {left right : State mode}
    (same : StateAgree mode region left right) : StateAgree mode region right left :=
  ⟨same.1.symm, same.2.1.symm, same.2.2.1.symm, same.2.2.2.1.symm,
    agree_symm region same.2.2.2.2⟩

theorem read_address_agrees (mode : Mode) (region : Region) (form : Form mode)
    (left right : State mode) (same : StateAgree mode region left right) :
    readAddress mode form left = readAddress mode form right := by
  cases form with
  | moffs address => rfl
  | exchangeIndirect => exact congrArg some same.2.1
  | callRelative displacement => rfl
  | memory operation displacement =>
    cases operation <;> simp only [readAddress, nextPC, same.1]

theorem read_within_agrees (mode : Mode) (region : Region) (form : Form mode)
    (left right : State mode) (same : StateAgree mode region left right) :
    ReadWithin mode region form left ↔ ReadWithin mode region form right := by
  simp only [ReadWithin, read_address_agrees mode region form left right same]

theorem fetch_within_agrees (mode : Mode) (region : Region) (left right : State mode)
    (same : StateAgree mode region left right) (header : region.Contains right.pc.toNat 3) :
    FetchWithin mode region left ↔ FetchWithin mode region right := by
  have bytes := bytes_agree region same.2.2.2.2 right.pc.toNat 3 header
  simp only [FetchWithin, same.1, bytes]

/-- Safety is itself independent of the exterior completion. -/
theorem safe_agrees (mode : Mode) (region : Region) (form : Form mode)
    (left right : State mode) (same : StateAgree mode region left right)
    (safe : Safe mode region form right) : Safe mode region form left :=
  ⟨(fetch_within_agrees mode region left right same safe.1.1).mpr safe.1,
    (read_within_agrees mode region form left right same).mpr safe.2.1,
    by rw [write_address_agrees mode region form left right same]; exact safe.2.2⟩

/-- Each footprint is computed at the actual successive state, after all prior
self-modifying writes. This is not a condition on the original packet snapshot. -/
@[expose] def SafeRun (mode : Mode) (region : Region) : List (Form mode) → State mode → Prop
  | [], _ => True
  | form :: rest, state => Safe mode region form state ∧ SafeRun mode region rest (execute mode form state)

theorem trace_agrees (mode : Mode) (region : Region) {right finish : State mode} {forms : List (Form mode)}
    (trace : Fetch.Trace mode right forms finish) (safe : SafeRun mode region forms right)
    (left : State mode) (same : StateAgree mode region left right) :
    Fetch.Trace mode left forms (runForms mode forms left) ∧
      StateAgree mode region (runForms mode forms left) finish := by
  induction trace generalizing left with
  | nil => exact ⟨Fetch.Trace.nil left, same⟩
  | @step state finish form rest fetched tail ih =>
    have fetchedLeft := (fetch_agrees mode region left state same safe.1.1).trans fetched
    have executed := execute_agrees mode region form left state same safe.1.2.1
    have continued := ih safe.2 (execute mode form left) executed
    exact ⟨Fetch.Trace.step fetchedLeft continued.1, continued.2⟩

/-- Whole-run ownership transfers with the identical computed write addresses. -/
theorem owned_run_agrees (mode : Mode) (region : Region) (owned : Word mode → Prop)
    (forms : List (Form mode)) (left right : State mode) (same : StateAgree mode region left right)
    (safe : SafeRun mode region forms right) (writes : Writes.OwnedRun mode owned forms right) :
    Writes.OwnedRun mode owned forms left := by
  induction forms generalizing left right with
  | nil => trivial
  | cons form rest ih =>
    refine ⟨?_, ih (execute mode form left) (execute mode form right)
      (execute_agrees mode region form left right same safe.1.2.1) safe.2 writes.2⟩
    rw [write_address_agrees mode region form left right same]
    exact writes.1

/-- All unloaded bytes are framed along a safe execution, rather than merely
unobserved by the final projection. -/
theorem run_outside (mode : Mode) (region : Region) (forms : List (Form mode)) (state : State mode)
    (safe : SafeRun mode region forms state) (position : Nat)
    (outside : ¬(region.lower ≤ position ∧ position < region.upper)) :
    (runForms mode forms state).memory position = state.memory position := by
  induction forms generalizing state with
  | nil => rfl
  | cons form rest ih =>
    rw [runForms, ih (execute mode form state) safe.2]
    rw [Writes.execute_memory]
    exact put_word_outside mode region state.memory _ _ safe.1.2.2 position outside

end SmcTuring.Native.RegionExecution

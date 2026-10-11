module
public import SmcTuring.Appendix.BytePacking

public section

namespace SmcTuring.Appendix.ByteProgram

open ByteImage
abbrev Instruction := Machine32.Instruction
abbrev State := ByteExecution.State

/-- Fixed source operations retain their whole encoding. Only field-consuming
AND/XOR forms own their actual imm32; the initial word is just a storage seed. -/
@[expose] def packet : Instruction → Packet
  | .store field value => .fixed (.immediate .store (FieldRefinement.address field) value)
  | .exchange field => .fixed (.memory .exchangeAcc (FieldRefinement.address field))
  | .xorConstant field value => .fixed (.immediate .bitXor (FieldRefinement.address field) value)
  | .subtractAcc field => .fixed (.memory .subtractAcc (FieldRefinement.address field))
  | .addAcc field => .fixed (.memory .addAcc (FieldRefinement.address field))
  | .negate field => .fixed (.memory .negate (FieldRefinement.address field))
  | .sbbZero field => .fixed (.memory .sbbZero (FieldRefinement.address field))
  | .complement field => .fixed (.memory .complement (FieldRefinement.address field))
  | .andField field _ => .immediate .bitAnd (FieldRefinement.address field) 0x80000000
  | .xorField field _ => .immediate .bitXor (FieldRefinement.address field) 0x80000000

@[expose] def bytes (instruction : Instruction) : Nat := (ByteCode.encode (packet instruction).initial).length
@[expose] def span (program : List Instruction) : Nat := BytePacking.size (program.map packet)
@[expose] def entries (start : Nat) (program : List Instruction) : List Entry := BytePacking.place start (program.map packet)

/-- Every dynamic source field is precisely the executing instruction's own
imm32. This is a STATIC offset condition, not an execution/readiness premise. -/
@[expose] def OwnOperand : Instruction → Nat → Prop
  | .andField _ source, pc | .xorField _ source, pc => source = pc + 6
  | _, _ => True

@[expose] def Linked : Nat → List Instruction → Prop
  | _, [] => True
  | pc, instruction :: rest => OwnOperand instruction pc ∧ Linked (pc + bytes instruction) rest

theorem span_cons (instruction : Instruction) (rest : List Instruction) :
    span (instruction :: rest) = bytes instruction + span rest := rfl

theorem instruction_length (instruction : Instruction) (native : State) :
    ByteCode.instructionLength (FieldRefinement.translate instruction native) = bytes instruction := by
  cases instruction <;> simp [bytes, packet, FieldRefinement.translate, Packet.initial,
    ByteCode.encode_length, ByteCode.instructionLength]

theorem current_translation (instruction : Instruction) (pc : Nat) (native : State)
    (own : OwnOperand instruction pc)
    (capacity : ∀ field ∈ FieldRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32) :
    current ⟨pc, packet instruction⟩ native.memory = FieldRefinement.translate instruction native := by
  cases instruction <;> try rfl
  all_goals
    simp only [OwnOperand] at own
    simp only [packet, current, FieldRefinement.translate]
    rw [←own, word_at_read_field native _ (capacity _ (by
      simp [FieldRefinement.dependencies, FieldRefinement.sources]))]

theorem execute_pc (instruction : Instruction) (pc : Nat) (native : State)
    (location : native.pc = FieldRefinement.address pc) :
    (ByteExecution.execute (FieldRefinement.translate instruction native) native).pc =
      FieldRefinement.address (pc + bytes instruction) := by
  rw [ByteExecution.execute_pc]
  have linear : ByteExecution.pc (FieldRefinement.translate instruction native) native =
      BitVec.add native.pc (BitVec.ofNat 32 (ByteCode.instructionLength (FieldRefinement.translate instruction native))) := by
    cases instruction <;> rfl
  rw [linear, instruction_length, location]
  exact BitVec.ofNat_add_ofNat _ _

/-- Construct an actual current-byte fetch trace from an intact image and only
STATIC ownership/placement/own-immediate/capacity facts. The invariant is proved
again after each actual write; there is no future trace or future Ready premise. -/
theorem constructed_trace (whole : List Entry) (program : List Instruction) (start : Nat) (native : State)
    (separate : Separated whole) (intact : Intact whole native.memory)
    (placed : ∀ entry ∈ entries start program, entry ∈ whole)
    (linked : Linked start program)
    (capacity : ∀ instruction ∈ program, ∀ field ∈ FieldRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32)
    (codeFits : start + span program < 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (Machine32.destination instruction))
    (location : native.pc = FieldRefinement.address start) :
    ByteExecution.Trace native (FieldRefinement.forms program native) (FieldRefinement.run program native) := by
  induction program generalizing start native with
  | nil => exact .nil native
  | cons instruction rest ih =>
    have headMember : (⟨start, packet instruction⟩ : Entry) ∈ whole := placed _ (by simp [entries, BytePacking.place])
    have headCapacity := capacity instruction (by simp)
    have exactForm := current_translation instruction start native linked.1 headCapacity
    have fetched : ByteCode.fetch native.memory native.pc.toNat =
        some (FieldRefinement.translate instruction native) := by
      have startFits : start + 4 ≤ 2 ^ 32 := by
        rw [span_cons] at codeFits
        have positive : 4 ≤ bytes instruction := by
          rw [←instruction_length instruction native]
          cases instruction <;> simp [FieldRefinement.translate, ByteCode.instructionLength, ByteCode.MemoryOp.trailer]
        omega
      rw [location]
      change ByteCode.fetch native.memory (FieldRefinement.address start).toNat =
        some (FieldRefinement.translate instruction native)
      rw [FieldRefinement.address_toNat start startFits]
      rw [←exactForm]
      exact fetch_current _ _ (intact _ headMember)
    have nextIntact : Intact whole (ByteExecution.execute (FieldRefinement.translate instruction native) native).memory := by
      apply execute_intact whole native _ separate intact
      rw [FieldRefinement.translate_destination,
        FieldRefinement.address_toNat _ (headCapacity _ (FieldRefinement.destination_dependency instruction))]
      exact ownership instruction (by simp)
    have tailPlaced : ∀ entry ∈ entries (start + bytes instruction) rest, entry ∈ whole := by
      intro entry member
      exact placed entry (by simpa only [entries, List.map_cons, BytePacking.place, bytes, List.mem_cons] using Or.inr member)
    have tailFits : start + bytes instruction + span rest < 2 ^ 32 := by
      simpa only [span_cons, Nat.add_assoc] using codeFits
    exact .step fetched (ih _ _ nextIntact tailPlaced linked.2
      (fun next member => capacity next (by simp [member])) tailFits
      (fun next member => ownership next (by simp [member])) (execute_pc instruction start native location))

/-- A single literal initializer supplies the initial invariant. All later
fetches above are constructed from actual evolving bytes. -/
theorem image_trace (whole : List Entry) (program : List Instruction) (start : Nat) (backing : Memory) (native : State)
    (separate : Separated whole)
    (initial : native.memory = image whole backing)
    (placed : ∀ entry ∈ entries start program, entry ∈ whole)
    (linked : Linked start program)
    (capacity : ∀ instruction ∈ program, ∀ field ∈ FieldRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32)
    (codeFits : start + span program < 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (Machine32.destination instruction))
    (location : native.pc = FieldRefinement.address start) :
    ByteExecution.Trace native (FieldRefinement.forms program native) (FieldRefinement.run program native) := by
  apply constructed_trace whole program start native separate _ placed linked capacity codeFits ownership location
  rw [initial]
  exact initialized_intact whole backing separate

theorem run_pc (program : List Instruction) (start : Nat) (native : State)
    (location : native.pc = FieldRefinement.address start) :
    (FieldRefinement.run program native).pc = FieldRefinement.address (start + span program) := by
  induction program generalizing start native with
  | nil => simpa only [FieldRefinement.run, span, BytePacking.size, List.map_nil, List.sum_nil, Nat.add_zero] using location
  | cons instruction rest ih =>
    have next := ih (start + bytes instruction) _ (execute_pc instruction start native location)
    simpa only [FieldRefinement.run, span_cons, Nat.add_assoc] using next

end SmcTuring.Appendix.ByteProgram

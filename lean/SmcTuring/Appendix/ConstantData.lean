module
public import SmcTuring.Appendix.ConstantPacking
public import SmcTuring.Appendix.ConstantRefinement
public import SmcTuring.Appendix.MultiplyData

public section
namespace SmcTuring.Appendix.ConstantData

open ConstantImage
abbrev Instruction := ConstantWords.Instruction
abbrev State := ConstantByteExecution.State

/-- Same literal store/exchange/use-accumulator/ADD operands as Listing 6.
    The final ADD owns its immediate; variable SHL packets are fixed. -/
@[expose] def packet : Instruction -> Packet
  | .selected op => .common (MultiplyLayout.dataPacket (.selected op))
  | .storeAcc field => .fixed (.common (.common (.storeAcc (FieldRefinement.address field))))
  | .shiftLeft field count => .fixed
      (if count = 1 then .common (.shiftLeft (FieldRefinement.address field))
       else .shiftImmediate (FieldRefinement.address field) (ConstantRefinement.countOf count))
  | .addFrom field _ => .common (.addImmediate (FieldRefinement.address field) 0x12345678)

@[expose] def bytes (instruction : Instruction) : Nat :=
  (ConstantByteCode.encode (packet instruction).initial).length
@[expose] def span (program : List Instruction) : Nat := ConstantPacking.size (program.map packet)
@[expose] def entries (start : Nat) (program : List Instruction) : List Entry :=
  ConstantPacking.place start (program.map packet)

/-- Static identity of each runtime immediate and its own owner location. -/
@[expose] def OwnOperand : Instruction -> Nat -> Prop
  | .selected (.andField _ source), pc | .selected (.xorField _ source), pc => source = pc + 6
  | .addFrom _ source, pc => source = pc + 6
  | _, _ => True

@[expose] def Linked : Nat -> List Instruction -> Prop
  | _, [] => True
  | pc, op :: rest => OwnOperand op pc ∧ Linked (pc + bytes op) rest

theorem span_cons (instruction : Instruction) (rest : List Instruction) :
    span (instruction :: rest) = bytes instruction + span rest := rfl

theorem instruction_length (instruction : Instruction) (native : State) :
    ConstantByteCode.instructionLength (ConstantRefinement.translate instruction native) = bytes instruction := by
  cases instruction with
  | selected op => exact MultiplyData.instruction_length (.selected op) native
  | storeAcc field => rfl
  | addFrom field source => rfl
  | shiftLeft field count =>
      simp only [ConstantRefinement.translate, bytes, packet]
      split <;> rfl

theorem current_translation (instruction : Instruction) (pc : Nat) (native : State)
    (own : OwnOperand instruction pc)
    (capacity : ∀ field ∈ ConstantRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32) :
    current ⟨pc, packet instruction⟩ native.memory = ConstantRefinement.translate instruction native := by
  cases instruction with
  | selected op =>
      have oldOwn : MultiplyData.OwnOperand (.selected op) pc := by
        cases op <;> exact own
      exact congrArg ConstantByteCode.Form.common
        (MultiplyData.current_translation (.selected op) pc native oldOwn capacity)
  | storeAcc field => rfl
  | shiftLeft field count =>
      simp only [packet, current, ConstantRefinement.translate]
  | addFrom field source =>
      simp only [OwnOperand] at own
      simp only [packet, current, MultiplyImage.current, ConstantRefinement.translate]
      rw [←own, ByteImage.word_at_read_field native _ (capacity _ (by simp [ConstantRefinement.dependencies]))]

theorem execute_pc (instruction : Instruction) (pc : Nat) (native : State)
    (location : native.pc = FieldRefinement.address pc) :
    (ConstantByteExecution.execute (ConstantRefinement.translate instruction native) native).pc =
      FieldRefinement.address (pc + bytes instruction) := by
  rw [ConstantRefinement.execute_pc, location]
  have length : bytes instruction = ConstantRefinement.dataLength instruction := by
    rw [←instruction_length instruction native, ConstantRefinement.translate_length]
  rw [length]
  exact BitVec.ofNat_add_ofNat _ _

/-- Construct an actual current-byte fetch trace from an intact image and only
STATIC ownership/placement/own-immediate/capacity facts. The invariant is proved
again after each actual write; there is no future trace or future Ready premise. -/
theorem constructed_trace (whole : List Entry) (program : List Instruction) (start : Nat) (native : State)
    (separate : Separated whole) (intact : Intact whole native.memory)
    (placed : ∀ entry ∈ entries start program, entry ∈ whole)
    (linked : Linked start program)
    (capacity : ∀ instruction ∈ program, ∀ field ∈ ConstantRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32)
    (codeFits : start + span program < 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (ConstantWords.destination instruction))
    (location : native.pc = FieldRefinement.address start) :
    ConstantByteExecution.Trace native (ConstantRefinement.forms program native) (ConstantRefinement.run program native) := by
  induction program generalizing start native with
  | nil => exact .nil native
  | cons instruction rest ih =>
    have headMember : (⟨start, packet instruction⟩ : Entry) ∈ whole := placed _ (by simp [entries, ConstantPacking.place])
    have headCapacity := capacity instruction (by simp)
    have exactForm := current_translation instruction start native linked.1 headCapacity
    have fetched : ConstantByteCode.fetch native.memory native.pc.toNat =
        some (ConstantRefinement.translate instruction native) := by
      have startFits : start + 4 ≤ 2 ^ 32 := by
        rw [span_cons] at codeFits
        have positive : 4 ≤ bytes instruction := by
          rw [←instruction_length instruction native]
          rw [ConstantRefinement.translate_length]
          cases instruction with
          | selected instruction => cases instruction <;> simp [ConstantRefinement.dataLength, MultiplyControl.dataLength]
          | shiftLeft field count => simp only [ConstantRefinement.dataLength]; split <;> omega
          | _ => simp [ConstantRefinement.dataLength]
        omega
      rw [location]
      change ConstantByteCode.fetch native.memory (FieldRefinement.address start).toNat =
        some (ConstantRefinement.translate instruction native)
      rw [FieldRefinement.address_toNat start startFits]
      rw [←exactForm]
      exact fetch_current _ _ (intact _ headMember)
    have nextIntact : Intact whole (ConstantByteExecution.execute (ConstantRefinement.translate instruction native) native).memory := by
      apply execute_intact whole native _ separate intact
      rw [ConstantRefinement.translate_destination,
        FieldRefinement.address_toNat _ (headCapacity _ (ConstantRefinement.destination_dependency instruction))]
      exact ownership instruction (by simp)
    have tailPlaced : ∀ entry ∈ entries (start + bytes instruction) rest, entry ∈ whole := by
      intro entry member
      exact placed entry (by simpa only [entries, List.map_cons, ConstantPacking.place, bytes, List.mem_cons] using Or.inr member)
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
    (capacity : ∀ instruction ∈ program, ∀ field ∈ ConstantRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32)
    (codeFits : start + span program < 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (ConstantWords.destination instruction))
    (location : native.pc = FieldRefinement.address start) :
    ConstantByteExecution.Trace native (ConstantRefinement.forms program native) (ConstantRefinement.run program native) := by
  apply constructed_trace whole program start native separate _ placed linked capacity codeFits ownership location
  rw [initial]
  exact initialized_intact whole backing separate

theorem run_pc (program : List Instruction) (start : Nat) (native : State)
    (location : native.pc = FieldRefinement.address start) :
    (ConstantRefinement.run program native).pc = FieldRefinement.address (start + span program) := by
  induction program generalizing start native with
  | nil => simpa only [ConstantRefinement.run, span, ConstantPacking.size, List.map_nil, List.sum_nil, Nat.add_zero] using location
  | cons instruction rest ih =>
    have next := ih (start + bytes instruction) _ (execute_pc instruction start native location)
    simpa only [ConstantRefinement.run, span_cons, Nat.add_assoc] using next


theorem run_intact (whole : List Entry) (program : List Instruction) (native : State)
    (separate : Separated whole) (intact : Intact whole native.memory)
    (capacity : ∀ instruction ∈ program, ConstantWords.destination instruction + 4 ≤ 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (ConstantWords.destination instruction)) :
    Intact whole (ConstantRefinement.run program native).memory := by
  induction program generalizing native with
  | nil => exact intact
  | cons instruction rest ih =>
      have next : Intact whole (ConstantByteExecution.execute (ConstantRefinement.translate instruction native) native).memory := by
        apply execute_intact whole native _ separate intact
        rw [ConstantRefinement.translate_destination,
          FieldRefinement.address_toNat _ (capacity instruction (by simp))]
        exact ownership instruction (by simp)
      exact ih _ next (fun op member => capacity op (by simp [member]))
        (fun op member => ownership op (by simp [member]))


end SmcTuring.Appendix.ConstantData

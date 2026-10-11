module
public import SmcTuring.Appendix.MultiplyLayout

public section
namespace SmcTuring.Appendix.MultiplyData

open MultiplyImage
abbrev Instruction := MultiplyWords.Instruction
abbrev State := MultiplyByteExecution.State
abbrev packet := MultiplyLayout.dataPacket

@[expose] def bytes (instruction : Instruction) : Nat :=
  (MultiplyByteCode.encode (packet instruction).initial).length
@[expose] def span (program : List Instruction) : Nat := MultiplyPacking.size (program.map packet)
@[expose] def entries (start : Nat) (program : List Instruction) : List Entry :=
  MultiplyPacking.place start (program.map packet)

/-- Only static own-operand identities, derived for each printed data block. -/
@[expose] def OwnOperand : Instruction → Nat → Prop
  | .selected (.andField _ source), pc | .selected (.xorField _ source), pc => source = pc + 6
  | .selfStore field, pc => field = pc + 6
  | .copyFrom _ source, pc | .addFrom _ source, pc => source = pc + 6
  | _, _ => True

@[expose] def Linked : Nat → List Instruction → Prop
  | _, [] => True
  | pc, instruction :: rest => OwnOperand instruction pc ∧ Linked (pc + bytes instruction) rest

theorem span_cons (instruction : Instruction) (rest : List Instruction) :
    span (instruction :: rest) = bytes instruction + span rest := rfl

theorem instruction_length (instruction : Instruction) (native : State) :
    MultiplyByteCode.instructionLength (MultiplyRefinement.translate instruction native) = bytes instruction := by
  rw [bytes, MultiplyLayout.data_initial, MultiplyByteCode.encode_length, MultiplyPackets.literal_length]
  exact MultiplyRefinement.translate_length instruction native

theorem current_translation (instruction : Instruction) (pc : Nat) (native : State)
    (own : OwnOperand instruction pc)
    (capacity : ∀ field ∈ MultiplyRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32) :
    current ⟨pc, packet instruction⟩ native.memory = MultiplyRefinement.translate instruction native := by
  cases instruction with
  | selected operation =>
    cases operation <;> try rfl
    all_goals
      simp only [OwnOperand] at own
      simp only [packet, MultiplyLayout.dataPacket, current, ByteImage.current,
        MultiplyRefinement.translate, FieldRefinement.translate]
      rw [←own, ByteImage.word_at_read_field native _ (capacity _ (by
        simp [MultiplyRefinement.dependencies,
          FieldRefinement.dependencies, FieldRefinement.sources]))]
  | selfStore field =>
    simp only [OwnOperand] at own
    simp only [packet, MultiplyLayout.dataPacket, current, ByteImage.current,
      MultiplyRefinement.translate]
    rw [←own, ByteImage.word_at_read_field native _ (capacity _ (by
      simp [MultiplyRefinement.dependencies, MultiplyWords.destination]))]
  | copyFrom field source =>
    simp only [OwnOperand] at own
    simp only [packet, MultiplyLayout.dataPacket, current, ByteImage.current,
      MultiplyRefinement.translate]
    rw [←own, ByteImage.word_at_read_field native _ (capacity _ (by
      simp [MultiplyRefinement.dependencies]))]
  | addFrom field source =>
    simp only [OwnOperand] at own
    simp only [packet, MultiplyLayout.dataPacket, current,
      MultiplyRefinement.translate]
    rw [←own, ByteImage.word_at_read_field native _ (capacity _ (by
      simp [MultiplyRefinement.dependencies]))]
  | _ => rfl

theorem execute_pc (instruction : Instruction) (pc : Nat) (native : State)
    (location : native.pc = FieldRefinement.address pc) :
    (MultiplyByteExecution.execute (MultiplyRefinement.translate instruction native) native).pc =
      FieldRefinement.address (pc + bytes instruction) := by
  rw [MultiplyRefinement.execute_pc, location]
  have length : bytes instruction = MultiplyControl.dataLength instruction := by
    rw [←instruction_length instruction native, MultiplyRefinement.translate_length]
  rw [length]
  exact BitVec.ofNat_add_ofNat _ _

/-- Construct an actual current-byte fetch trace from an intact image and only
STATIC ownership/placement/own-immediate/capacity facts. The invariant is proved
again after each actual write; there is no future trace or future Ready premise. -/
theorem constructed_trace (whole : List Entry) (program : List Instruction) (start : Nat) (native : State)
    (separate : Separated whole) (intact : Intact whole native.memory)
    (placed : ∀ entry ∈ entries start program, entry ∈ whole)
    (linked : Linked start program)
    (capacity : ∀ instruction ∈ program, ∀ field ∈ MultiplyRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32)
    (codeFits : start + span program < 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (MultiplyWords.destination instruction))
    (location : native.pc = FieldRefinement.address start) :
    MultiplyByteExecution.Trace native (MultiplyRefinement.forms program native) (MultiplyRefinement.run program native) := by
  induction program generalizing start native with
  | nil => exact .nil native
  | cons instruction rest ih =>
    have headMember : (⟨start, packet instruction⟩ : Entry) ∈ whole := placed _ (by simp [entries, MultiplyPacking.place])
    have headCapacity := capacity instruction (by simp)
    have exactForm := current_translation instruction start native linked.1 headCapacity
    have fetched : MultiplyByteCode.fetch native.memory native.pc.toNat =
        some (MultiplyRefinement.translate instruction native) := by
      have startFits : start + 4 ≤ 2 ^ 32 := by
        rw [span_cons] at codeFits
        have positive : 4 ≤ bytes instruction := by
          rw [←instruction_length instruction native]
          rw [MultiplyRefinement.translate_length]
          cases instruction with
          | selected instruction => cases instruction <;> simp [MultiplyControl.dataLength]
          | _ => simp [MultiplyControl.dataLength]
        omega
      rw [location]
      change MultiplyByteCode.fetch native.memory (FieldRefinement.address start).toNat =
        some (MultiplyRefinement.translate instruction native)
      rw [FieldRefinement.address_toNat start startFits]
      rw [←exactForm]
      exact fetch_current _ _ (intact _ headMember)
    have nextIntact : Intact whole (MultiplyByteExecution.execute (MultiplyRefinement.translate instruction native) native).memory := by
      apply execute_intact whole native _ separate intact
      rw [MultiplyRefinement.translate_destination,
        FieldRefinement.address_toNat _ (headCapacity _ (MultiplyRefinement.destination_dependency instruction))]
      exact ownership instruction (by simp)
    have tailPlaced : ∀ entry ∈ entries (start + bytes instruction) rest, entry ∈ whole := by
      intro entry member
      exact placed entry (by simpa only [entries, List.map_cons, MultiplyPacking.place, bytes, List.mem_cons] using Or.inr member)
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
    (capacity : ∀ instruction ∈ program, ∀ field ∈ MultiplyRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32)
    (codeFits : start + span program < 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (MultiplyWords.destination instruction))
    (location : native.pc = FieldRefinement.address start) :
    MultiplyByteExecution.Trace native (MultiplyRefinement.forms program native) (MultiplyRefinement.run program native) := by
  apply constructed_trace whole program start native separate _ placed linked capacity codeFits ownership location
  rw [initial]
  exact initialized_intact whole backing separate

theorem run_pc (program : List Instruction) (start : Nat) (native : State)
    (location : native.pc = FieldRefinement.address start) :
    (MultiplyRefinement.run program native).pc = FieldRefinement.address (start + span program) := by
  induction program generalizing start native with
  | nil => simpa only [MultiplyRefinement.run, span, MultiplyPacking.size, List.map_nil, List.sum_nil, Nat.add_zero] using location
  | cons instruction rest ih =>
    have next := ih (start + bytes instruction) _ (execute_pc instruction start native location)
    simpa only [MultiplyRefinement.run, span_cons, Nat.add_assoc] using next


@[expose] def blockStart (place : MultiplyPackets.Placement) : MultiplyBlocks.Block → Nat
  | .initial => place.origin
  | .guard => place.origin + 85
  | .body => place.origin + 191
  | .finish => place.origin + 362

theorem block_linked (place : MultiplyPackets.Placement) (block : MultiplyBlocks.Block) :
    Linked (blockStart place block) (MultiplyBlocks.words (MultiplyPackets.layout place) block) := by
  cases block <;> simp [blockStart, MultiplyBlocks.words, MultiplyWords.initialProgram,
    MultiplyWords.copyProgram, MultiplyWords.guard, MultiplyWords.body, MultiplyWords.finish,
    Linked, OwnOperand, bytes, packet, MultiplyLayout.data_initial, MultiplyByteCode.encode_length,
    MultiplyPackets.literal_length, MultiplyControl.dataLength, MultiplyPackets.layout,
    MultiplyPackets.fields, Nat.add_assoc]

theorem block_dependency_owned (place : MultiplyPackets.Placement) (x y : MultiplyByteCode.Word)
    (block : MultiplyBlocks.Block) :
    ∀ instruction ∈ MultiplyBlocks.words (MultiplyPackets.layout place) block,
      ∀ field ∈ MultiplyRefinement.dependencies instruction,
        Owned (MultiplyLayout.entries place x y) field := by
  cases block <;> simp [MultiplyBlocks.words, MultiplyWords.initialProgram,
    MultiplyWords.copyProgram, MultiplyWords.guard, MultiplyWords.body, MultiplyWords.finish,
    MultiplyRefinement.dependencies, MultiplyWords.destination, FieldRefinement.dependencies,
    FieldRefinement.sources, Machine32.destination, MultiplyPackets.layout, MultiplyLayout.slot_owned]

theorem block_capacity (place : MultiplyPackets.Placement) (x y : MultiplyByteCode.Word)
    (valid : MultiplyLayout.Admissible place) (block : MultiplyBlocks.Block) :
    ∀ instruction ∈ MultiplyBlocks.words (MultiplyPackets.layout place) block,
      ∀ field ∈ MultiplyRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32 := by
  intro instruction member field dependency
  exact (MultiplyLayout.field_layout place x y valid).fits field
    ((MultiplyPacking.fields_owned _ _).mpr (block_dependency_owned place x y block instruction member field dependency))

theorem block_placed (place : MultiplyPackets.Placement) (x y : MultiplyByteCode.Word)
    (block : MultiplyBlocks.Block) :
    ∀ entry ∈ entries (blockStart place block) (MultiplyBlocks.words (MultiplyPackets.layout place) block),
      entry ∈ MultiplyLayout.entries place x y := by
  intro entry member
  change entry ∈ MultiplyPacking.place (blockStart place block) (MultiplyLayout.dataPackets place block) at member
  apply (MultiplyRegions.member (MultiplyLayout.regions place x y) entry).mpr
  refine ⟨⟨place.origin, MultiplyLayout.purePackets place⟩, by simp [MultiplyLayout.regions], ?_⟩
  change entry ∈ MultiplyPacking.place place.origin (MultiplyLayout.purePackets place)
  simp only [MultiplyLayout.purePackets, MultiplyPacking.place_append, MultiplyPacking.size_append,
    MultiplyLayout.data_size, MultiplyLayout.tail_size, MultiplyLayout.restore_size,
    Nat.reduceAdd, List.mem_append]
  cases block <;> simp only [blockStart] at member
  all_goals tauto

theorem block_code_fits (place : MultiplyPackets.Placement) (valid : MultiplyLayout.Admissible place)
    (block : MultiplyBlocks.Block) :
    blockStart place block + span (MultiplyBlocks.words (MultiplyPackets.layout place) block) < 2 ^ 32 := by
  change blockStart place block + MultiplyPacking.size (MultiplyLayout.dataPackets place block) < 2 ^ 32
  rw [MultiplyLayout.data_size]
  rcases valid with ⟨h0,h1,h2,h3,h4⟩
  cases block <;> simp only [blockStart]
  all_goals omega

/-- Actual current-memory data fetches follow from the maintained original-image
invariant. All own-field, placement, code-write and capacity facts are derived
from the printed layout; no future packet or instruction trace is a premise. -/
theorem block_trace (place : MultiplyPackets.Placement) (x y : MultiplyByteCode.Word)
    (valid : MultiplyLayout.Admissible place) (block : MultiplyBlocks.Block) (native : State)
    (intact : Intact (MultiplyLayout.entries place x y) native.memory)
    (location : native.pc = FieldRefinement.address (blockStart place block)) :
    MultiplyByteExecution.Trace native
      (MultiplyRefinement.forms (MultiplyBlocks.words (MultiplyPackets.layout place) block) native)
      (MultiplyRefinement.run (MultiplyBlocks.words (MultiplyPackets.layout place) block) native) := by
  apply constructed_trace (MultiplyLayout.entries place x y) _ (blockStart place block) native
    (MultiplyLayout.separated place x y valid) intact (block_placed place x y block)
    (block_linked place block) (block_capacity place x y valid block) (block_code_fits place valid block) _ location
  intro instruction member
  exact block_dependency_owned place x y block instruction member _ (MultiplyRefinement.destination_dependency instruction)

theorem block_image_trace (place : MultiplyPackets.Placement) (x y : MultiplyByteCode.Word)
    (valid : MultiplyLayout.Admissible place) (block : MultiplyBlocks.Block) (backing : Memory) (native : State)
    (initial : native.memory = image (MultiplyLayout.entries place x y) backing)
    (location : native.pc = FieldRefinement.address (blockStart place block)) :
    MultiplyByteExecution.Trace native
      (MultiplyRefinement.forms (MultiplyBlocks.words (MultiplyPackets.layout place) block) native)
      (MultiplyRefinement.run (MultiplyBlocks.words (MultiplyPackets.layout place) block) native) := by
  apply block_trace place x y valid block native _ location
  rw [initial]
  exact MultiplyLayout.initial_intact place x y backing valid

theorem run_intact (whole : List Entry) (program : List Instruction) (native : State)
    (separate : Separated whole) (intact : Intact whole native.memory)
    (capacity : ∀ instruction ∈ program, MultiplyWords.destination instruction + 4 ≤ 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (MultiplyWords.destination instruction)) :
    Intact whole (MultiplyRefinement.run program native).memory := by
  induction program generalizing native with
  | nil => exact intact
  | cons instruction rest ih =>
      have next : Intact whole (MultiplyByteExecution.execute (MultiplyRefinement.translate instruction native) native).memory := by
        apply execute_intact whole native _ separate intact
        rw [MultiplyRefinement.translate_destination,
          FieldRefinement.address_toNat _ (capacity instruction (by simp))]
        exact ownership instruction (by simp)
      exact ih _ next (fun op member => capacity op (by simp [member]))
        (fun op member => ownership op (by simp [member]))

theorem block_intact (place : MultiplyPackets.Placement) (x y : MultiplyByteCode.Word)
    (valid : MultiplyLayout.Admissible place) (block : MultiplyBlocks.Block) (native : State)
    (intact : Intact (MultiplyLayout.entries place x y) native.memory) :
    Intact (MultiplyLayout.entries place x y)
      (MultiplyRefinement.run (MultiplyBlocks.words (MultiplyPackets.layout place) block) native).memory := by
  apply run_intact _ _ native (MultiplyLayout.separated place x y valid) intact
  · intro op member
    exact block_capacity place x y valid block op member _ (MultiplyRefinement.destination_dependency op)
  · intro op member
    exact block_dependency_owned place x y block op member _ (MultiplyRefinement.destination_dependency op)

theorem block_refinement (place : MultiplyPackets.Placement) (x y : MultiplyByteCode.Word)
    (valid : MultiplyLayout.Admissible place) (block : MultiplyBlocks.Block)
    (source : Machine32.State) (native : State)
    (agreement : FieldRefinement.Agreement (MultiplyPacking.fields (MultiplyLayout.entries place x y)) source native) :
    FieldRefinement.Agreement (MultiplyPacking.fields (MultiplyLayout.entries place x y))
      (MultiplyWords.run (MultiplyBlocks.words (MultiplyPackets.layout place) block) source)
      (MultiplyRefinement.run (MultiplyBlocks.words (MultiplyPackets.layout place) block) native) := by
  apply MultiplyRefinement.simulate_run (MultiplyLayout.field_layout place x y valid) _ source native agreement
  intro op member field dependency
  exact (MultiplyPacking.fields_owned _ _).mpr (block_dependency_owned place x y block op member field dependency)

end SmcTuring.Appendix.MultiplyData

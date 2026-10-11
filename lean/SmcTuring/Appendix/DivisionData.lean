module
public import SmcTuring.Appendix.DivisionLayout
public import SmcTuring.Appendix.MultiplyData
public import SmcTuring.Appendix.DivisionLinear

public section
namespace SmcTuring.Appendix.DivisionData

open DivisionImage
abbrev Instruction := DivisionWords.Instruction
abbrev State := DivisionByteExecution.State
abbrev packet := DivisionLayout.dataPacket

@[expose] def bytes (instruction : Instruction) : Nat :=
  (DivisionByteCode.encode (packet instruction).initial).length
@[expose] def span (program : List Instruction) : Nat := DivisionPacking.size (program.map packet)
@[expose] def entries (start : Nat) (program : List Instruction) : List Entry :=
  DivisionPacking.place start (program.map packet)

/-- Only static own-operand identities, derived for each printed data block. -/
@[expose] def OwnOperand : Instruction → Nat → Prop
  | .simple instruction, pc => MultiplyData.OwnOperand instruction pc
  | .subtractFrom _ source, pc => source = pc + 6
  | _, _ => True

@[expose] def Linked : Nat → List Instruction → Prop
  | _, [] => True
  | pc, instruction :: rest => OwnOperand instruction pc ∧ Linked (pc + bytes instruction) rest

theorem span_cons (instruction : Instruction) (rest : List Instruction) :
    span (instruction :: rest) = bytes instruction + span rest := rfl

theorem instruction_length (instruction : Instruction) (native : State) :
    DivisionByteCode.instructionLength (DivisionRefinement.translate instruction native) = bytes instruction := by
  rw [bytes, DivisionLayout.data_initial, DivisionByteCode.encode_length, DivisionPackets.literal_length]
  exact DivisionRefinement.translate_length instruction native

theorem current_translation (instruction : Instruction) (pc : Nat) (native : State)
    (own : OwnOperand instruction pc)
    (capacity : ∀ field ∈ DivisionRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32) :
    current ⟨pc, packet instruction⟩ native.memory = DivisionRefinement.translate instruction native := by
  cases instruction with
  | simple instruction =>
      exact congrArg DivisionByteCode.Form.common (MultiplyData.current_translation instruction pc native own capacity)
  | subtractFrom field source =>
    simp only [OwnOperand] at own
    simp only [packet, DivisionLayout.dataPacket, current, DivisionRefinement.translate]
    rw [←own, ByteImage.word_at_read_field native _ (capacity _ (by
      simp [DivisionRefinement.dependencies]))]
  | _ => rfl

theorem execute_pc (instruction : Instruction) (pc : Nat) (native : State)
    (location : native.pc = FieldRefinement.address pc) :
    (DivisionByteExecution.execute (DivisionRefinement.translate instruction native) native).pc =
      FieldRefinement.address (pc + bytes instruction) := by
  rw [DivisionRefinement.execute_pc, location]
  have length : bytes instruction = DivisionControl.dataLength instruction := by
    rw [←instruction_length instruction native, DivisionRefinement.translate_length]
  rw [length]
  exact BitVec.ofNat_add_ofNat _ _

/-- Construct an actual current-byte fetch trace from an intact image and only
STATIC ownership/placement/own-immediate/capacity facts. The invariant is proved
again after each actual write; there is no future trace or future Ready premise. -/
theorem constructed_trace (whole : List Entry) (program : List Instruction) (start : Nat) (native : State)
    (separate : Separated whole) (intact : Intact whole native.memory)
    (placed : ∀ entry ∈ entries start program, entry ∈ whole)
    (linked : Linked start program)
    (capacity : ∀ instruction ∈ program, ∀ field ∈ DivisionRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32)
    (codeFits : start + span program < 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (DivisionWords.destination instruction))
    (location : native.pc = FieldRefinement.address start) :
    DivisionByteExecution.Trace native (DivisionRefinement.forms program native) (DivisionRefinement.run program native) := by
  induction program generalizing start native with
  | nil => exact .nil native
  | cons instruction rest ih =>
    have headMember : (⟨start, packet instruction⟩ : Entry) ∈ whole := placed _ (by simp [entries, DivisionPacking.place])
    have headCapacity := capacity instruction (by simp)
    have exactForm := current_translation instruction start native linked.1 headCapacity
    have fetched : DivisionByteCode.fetch native.memory native.pc.toNat =
        some (DivisionRefinement.translate instruction native) := by
      have startFits : start + 4 ≤ 2 ^ 32 := by
        rw [span_cons] at codeFits
        have positive : 4 ≤ bytes instruction := by
          rw [←instruction_length instruction native]
          exact DivisionLinear.minimum_length _
        omega
      rw [location]
      change DivisionByteCode.fetch native.memory (FieldRefinement.address start).toNat =
        some (DivisionRefinement.translate instruction native)
      rw [FieldRefinement.address_toNat start startFits]
      rw [←exactForm]
      exact fetch_current _ _ (intact _ headMember)
    have nextIntact : Intact whole (DivisionByteExecution.execute (DivisionRefinement.translate instruction native) native).memory := by
      apply execute_intact whole native _ separate intact
      rw [DivisionRefinement.translate_destination,
        FieldRefinement.address_toNat _ (headCapacity _ (DivisionRefinement.destination_dependency instruction))]
      exact ownership instruction (by simp)
    have tailPlaced : ∀ entry ∈ entries (start + bytes instruction) rest, entry ∈ whole := by
      intro entry member
      exact placed entry (by simpa only [entries, List.map_cons, DivisionPacking.place, bytes, List.mem_cons] using Or.inr member)
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
    (capacity : ∀ instruction ∈ program, ∀ field ∈ DivisionRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32)
    (codeFits : start + span program < 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (DivisionWords.destination instruction))
    (location : native.pc = FieldRefinement.address start) :
    DivisionByteExecution.Trace native (DivisionRefinement.forms program native) (DivisionRefinement.run program native) := by
  apply constructed_trace whole program start native separate _ placed linked capacity codeFits ownership location
  rw [initial]
  exact initialized_intact whole backing separate

theorem run_pc (program : List Instruction) (start : Nat) (native : State)
    (location : native.pc = FieldRefinement.address start) :
    (DivisionRefinement.run program native).pc = FieldRefinement.address (start + span program) := by
  induction program generalizing start native with
  | nil => simpa only [DivisionRefinement.run, span, DivisionPacking.size, List.map_nil, List.sum_nil, Nat.add_zero] using location
  | cons instruction rest ih =>
    have next := ih (start + bytes instruction) _ (execute_pc instruction start native location)
    simpa only [DivisionRefinement.run, span_cons, Nat.add_assoc] using next


@[expose] def blockStart (place : DivisionPackets.Placement) : DivisionBlocks.Block → Nat
  | .initial => place.origin
  | .guard => place.origin + DivisionPackets.initialSpan place + 41
  | .body => place.origin + DivisionPackets.initialSpan place + 147
  | .finish => place.origin + DivisionPackets.initialSpan place + 365

theorem block_linked (place : DivisionPackets.Placement) (block : DivisionBlocks.Block) :
    Linked (blockStart place block) (DivisionBlocks.words (DivisionPackets.layout place) block) := by
  cases signed : place.signed <;> cases mod : place.mod <;> cases block <;>
    simp [blockStart, DivisionBlocks.words, DivisionWords.initializeData,
      DivisionWords.signPrefix, DivisionWords.sample, DivisionWords.normalize, DivisionWords.copy,
      MultiplyWords.copyProgram, DivisionGuard.program, MultiplyWords.guard, DivisionGuard.guardFields,
      DivisionGuard.binding, DivisionWords.body, DivisionWords.finishData, DivisionWords.selected,
      Linked, OwnOperand, MultiplyData.OwnOperand, bytes, packet, DivisionLayout.data_initial,
      DivisionByteCode.encode_length, DivisionPackets.literal_length, DivisionControl.dataLength,
      MultiplyControl.dataLength, DivisionPackets.layout, DivisionPackets.fields,
      DivisionPackets.initialSpan, DivisionPackets.signSpan, signed, mod, Nat.add_assoc, Nat.add_sub_assoc]

theorem block_dependency_owned (place : DivisionPackets.Placement) (x y : DivisionByteCode.Word)
    (block : DivisionBlocks.Block) :
    ∀ instruction ∈ DivisionBlocks.words (DivisionPackets.layout place) block,
      ∀ field ∈ DivisionRefinement.dependencies instruction,
        Owned (DivisionLayout.entries place x y) field := by
  cases signed : place.signed <;> cases mod : place.mod <;> cases block <;>
    simp [DivisionBlocks.words, DivisionWords.initializeData, DivisionWords.signPrefix,
      DivisionWords.sample, DivisionWords.normalize, DivisionWords.copy, MultiplyWords.copyProgram,
      DivisionGuard.program, MultiplyWords.guard, DivisionGuard.guardFields, DivisionGuard.binding,
      DivisionWords.body, DivisionWords.finishData, DivisionWords.selected,
      DivisionRefinement.dependencies, MultiplyRefinement.dependencies, DivisionWords.destination,
      MultiplyWords.destination, FieldRefinement.dependencies, FieldRefinement.sources, Machine32.destination,
      DivisionPackets.layout, signed, mod]
  all_goals repeat' apply And.intro
  all_goals apply DivisionLayout.slot_owned
  all_goals simp_all [DivisionLayout.ActiveSlot]

theorem block_capacity (place : DivisionPackets.Placement) (x y : DivisionByteCode.Word)
    (valid : DivisionLayout.Admissible place) (block : DivisionBlocks.Block) :
    ∀ instruction ∈ DivisionBlocks.words (DivisionPackets.layout place) block,
      ∀ field ∈ DivisionRefinement.dependencies instruction, field + 4 ≤ 2 ^ 32 := by
  intro instruction member field dependency
  exact (DivisionLayout.field_layout place x y valid).fits field
    ((DivisionPacking.fields_owned _ _).mpr (block_dependency_owned place x y block instruction member field dependency))

set_option maxRecDepth 4096 in
theorem block_placed (place : DivisionPackets.Placement) (x y : DivisionByteCode.Word)
    (block : DivisionBlocks.Block) :
    ∀ entry ∈ entries (blockStart place block) (DivisionBlocks.words (DivisionPackets.layout place) block),
      entry ∈ DivisionLayout.entries place x y := by
  intro entry member
  change entry ∈ DivisionPacking.place (blockStart place block) (DivisionLayout.dataPackets place block) at member
  apply (DivisionRegions.member (DivisionLayout.regions place x y) entry).mpr
  refine ⟨⟨place.origin, DivisionLayout.purePackets place⟩, by simp [DivisionLayout.regions], ?_⟩
  change entry ∈ DivisionPacking.place place.origin (DivisionLayout.purePackets place)
  simp only [DivisionLayout.purePackets, DivisionPacking.place_append, DivisionPacking.size_append,
    DivisionLayout.data_size, DivisionLayout.tail_size, DivisionLayout.restore_size,
    Nat.reduceAdd, Nat.add_assoc, List.mem_append]
  cases block <;> simp only [blockStart, Nat.add_assoc] at member
  all_goals tauto

theorem block_code_fits (place : DivisionPackets.Placement) (valid : DivisionLayout.Admissible place)
    (block : DivisionBlocks.Block) :
    blockStart place block + span (DivisionBlocks.words (DivisionPackets.layout place) block) < 2 ^ 32 := by
  change blockStart place block + DivisionPacking.size (DivisionLayout.dataPackets place block) < 2 ^ 32
  rw [DivisionLayout.data_size]
  rcases valid with ⟨h0,h1,h2,h3,h4,_⟩
  cases signed : place.signed <;> cases mod : place.mod <;> cases block <;>
    simp only [blockStart, DivisionPackets.initialSpan, signed, mod, Bool.false_eq_true,
      ite_true, ite_false, DivisionLayout.pureSpan] at *
  all_goals omega

/-- Actual current-memory data fetches follow from the maintained original-image
invariant. All own-field, placement, code-write and capacity facts are derived
from the printed layout; no future packet or instruction trace is a premise. -/
theorem block_trace (place : DivisionPackets.Placement) (x y : DivisionByteCode.Word)
    (valid : DivisionLayout.Admissible place) (block : DivisionBlocks.Block) (native : State)
    (intact : Intact (DivisionLayout.entries place x y) native.memory)
    (location : native.pc = FieldRefinement.address (blockStart place block)) :
    DivisionByteExecution.Trace native
      (DivisionRefinement.forms (DivisionBlocks.words (DivisionPackets.layout place) block) native)
      (DivisionRefinement.run (DivisionBlocks.words (DivisionPackets.layout place) block) native) := by
  apply constructed_trace (DivisionLayout.entries place x y) _ (blockStart place block) native
    (DivisionLayout.separated place x y valid) intact (block_placed place x y block)
    (block_linked place block) (block_capacity place x y valid block) (block_code_fits place valid block) _ location
  intro instruction member
  exact block_dependency_owned place x y block instruction member _ (DivisionRefinement.destination_dependency instruction)

theorem block_image_trace (place : DivisionPackets.Placement) (x y : DivisionByteCode.Word)
    (valid : DivisionLayout.Admissible place) (block : DivisionBlocks.Block) (backing : Memory) (native : State)
    (initial : native.memory = image (DivisionLayout.entries place x y) backing)
    (location : native.pc = FieldRefinement.address (blockStart place block)) :
    DivisionByteExecution.Trace native
      (DivisionRefinement.forms (DivisionBlocks.words (DivisionPackets.layout place) block) native)
      (DivisionRefinement.run (DivisionBlocks.words (DivisionPackets.layout place) block) native) := by
  apply block_trace place x y valid block native _ location
  rw [initial]
  exact DivisionLayout.initial_intact place x y backing valid

theorem run_intact (whole : List Entry) (program : List Instruction) (native : State)
    (separate : Separated whole) (intact : Intact whole native.memory)
    (capacity : ∀ instruction ∈ program, DivisionWords.destination instruction + 4 ≤ 2 ^ 32)
    (ownership : ∀ instruction ∈ program, Owned whole (DivisionWords.destination instruction)) :
    Intact whole (DivisionRefinement.run program native).memory := by
  induction program generalizing native with
  | nil => exact intact
  | cons instruction rest ih =>
      have next : Intact whole (DivisionByteExecution.execute (DivisionRefinement.translate instruction native) native).memory := by
        apply execute_intact whole native _ separate intact
        rw [DivisionRefinement.translate_destination,
          FieldRefinement.address_toNat _ (capacity instruction (by simp))]
        exact ownership instruction (by simp)
      exact ih _ next (fun op member => capacity op (by simp [member]))
        (fun op member => ownership op (by simp [member]))

theorem block_intact (place : DivisionPackets.Placement) (x y : DivisionByteCode.Word)
    (valid : DivisionLayout.Admissible place) (block : DivisionBlocks.Block) (native : State)
    (intact : Intact (DivisionLayout.entries place x y) native.memory) :
    Intact (DivisionLayout.entries place x y)
      (DivisionRefinement.run (DivisionBlocks.words (DivisionPackets.layout place) block) native).memory := by
  apply run_intact _ _ native (DivisionLayout.separated place x y valid) intact
  · intro op member
    exact block_capacity place x y valid block op member _ (DivisionRefinement.destination_dependency op)
  · intro op member
    exact block_dependency_owned place x y block op member _ (DivisionRefinement.destination_dependency op)

theorem block_refinement (place : DivisionPackets.Placement) (x y : DivisionByteCode.Word)
    (valid : DivisionLayout.Admissible place) (block : DivisionBlocks.Block)
    (source : Machine32.State) (native : State)
    (agreement : FieldRefinement.Agreement (DivisionPacking.fields (DivisionLayout.entries place x y)) source native) :
    FieldRefinement.Agreement (DivisionPacking.fields (DivisionLayout.entries place x y))
      (DivisionWords.run (DivisionBlocks.words (DivisionPackets.layout place) block) source)
      (DivisionRefinement.run (DivisionBlocks.words (DivisionPackets.layout place) block) native) := by
  apply DivisionRefinement.simulate_run (DivisionLayout.field_layout place x y valid) _ source native agreement
  intro op member field dependency
  exact (DivisionPacking.fields_owned _ _).mpr (block_dependency_owned place x y block op member field dependency)

theorem pure_destinations (codeField : Nat → Prop) (program : List Instruction)
    (source : Machine32.State) (pure : DivisionWords.PureRun codeField program source) :
    ∀ instruction ∈ program, codeField (DivisionWords.destination instruction) := by
  induction program generalizing source with
  | nil => simp
  | cons instruction rest ih =>
    intro next member
    rcases List.mem_cons.mp member with rfl | inTail
    · exact pure.1
    · exact ih _ pure.2 next inTail

end SmcTuring.Appendix.DivisionData

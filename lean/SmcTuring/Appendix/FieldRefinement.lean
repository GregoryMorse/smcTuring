module
public import SmcTuring.Appendix.Machine32
public import SmcTuring.Appendix.ByteExecution

public section

namespace SmcTuring.Appendix.FieldRefinement

abbrev Word := BitVec 32
abbrev State := ByteExecution.State
abbrev Instruction := Machine32.Instruction

@[expose] def address (field : Nat) : Word := BitVec.ofNat 32 field
@[expose] def readField (state : State) (field : Nat) : Word :=
  ByteExecution.prior state (address field)

/-- The view is finite: overlapping byte windows cannot represent globally
independent word cells. Each selected field must fit and distinct fields must
have disjoint complete four-byte windows. No alignment is silently assumed. -/
structure Layout (fields : List Nat) : Prop where
  fits : ∀ field ∈ fields, field + 4 ≤ 2 ^ 32
  separate : ∀ written ∈ fields, ∀ observed ∈ fields, written ≠ observed →
    written + 4 ≤ observed ∨ observed + 4 ≤ written

structure Agreement (fields : List Nat) (source : Machine32.State) (native : State) : Prop where
  accumulator : native.accumulator = source.accumulator
  carry : native.carry = source.carry
  words : ∀ field ∈ fields, readField native field = source.memory field

@[expose] def sources : Instruction → List Nat
  | .andField _ source | .xorField _ source => [source]
  | _ => []
@[expose] def dependencies (instruction : Instruction) : List Nat :=
  Machine32.destination instruction :: sources instruction

/-- Dynamic imm32 operands are read from the CURRENT byte memory. This is an
instruction-effect translation, not a constructed emitter/fetch trace: the later
literal-layout proof must identify these words with the own immediate fields. -/
@[expose] def translate (instruction : Instruction) (native : State) : ByteCode.Form :=
  match instruction with
  | .store field value => .immediate .store (address field) value
  | .exchange field => .memory .exchangeAcc (address field)
  | .xorConstant field value => .immediate .bitXor (address field) value
  | .subtractAcc field => .memory .subtractAcc (address field)
  | .addAcc field => .memory .addAcc (address field)
  | .negate field => .memory .negate (address field)
  | .sbbZero field => .memory .sbbZero (address field)
  | .complement field => .memory .complement (address field)
  | .andField field source => .immediate .bitAnd (address field) (readField native source)
  | .xorField field source => .immediate .bitXor (address field) (readField native source)

theorem destination_dependency (instruction : Instruction) :
    Machine32.destination instruction ∈ dependencies instruction := by simp [dependencies]

theorem address_toNat (field : Nat) (fits : field + 4 ≤ 2 ^ 32) :
    (address field).toNat = field := by
  have below : field < 2 ^ 32 := by omega
  simp only [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt below]

/-- Equal loaded words give equal ORIGINAL byte windows, without assuming
that either window was previously initialized by an encoder. -/
theorem equal_word_bytes (first second : State) (field : Nat) (fits : field + 4 ≤ 2 ^ 32)
    (words : readField first field = readField second field) :
    Native.ByteMemory.bytesAt first.memory field 4 = Native.ByteMemory.bytesAt second.memory field 4 := by
  have firstBytes := Native.LittleEndian.word_encode_decode Native.Mode.x86.wordBytes _ _
    (Native.Execution.read_word_total .x86 first.memory (address field))
  have secondBytes := Native.LittleEndian.word_encode_decode Native.Mode.x86.wordBytes _ _
    (Native.Execution.read_word_total .x86 second.memory (address field))
  have firstWindow : Native.LittleEndian.wordEncode 4 (readField first field) =
      Native.ByteMemory.bytesAt first.memory field 4 := by
    simpa only [readField, ByteExecution.prior, Native.Mode.wordBytes, address_toNat field fits] using firstBytes
  have secondWindow : Native.LittleEndian.wordEncode 4 (readField second field) =
      Native.ByteMemory.bytesAt second.memory field 4 := by
    simpa only [readField, ByteExecution.prior, Native.Mode.wordBytes, address_toNat field fits] using secondBytes
  rw [←firstWindow, ←secondWindow, words]

theorem equal_word_byte (first second : State) (field : Nat) (fits : field + 4 ≤ 2 ^ 32)
    (words : readField first field = readField second field) (position : Nat)
    (inside : Native.ByteMemory.Inside field 4 position) : first.memory position = second.memory position := by
  have below : position - field < 4 := by rcases inside with ⟨_, _⟩; omega
  have windows := equal_word_bytes first second field fits words
  have bytes := congrArg (fun packet : List Native.LittleEndian.Byte => packet[position - field]?) windows
  simp only [Native.ByteMemory.bytesAt, List.getElem?_ofFn, dite_eq_left below] at bytes
  simpa only [Nat.add_sub_of_le inside.1] using Option.some.inj bytes

theorem layout_outside {fields : List Nat} (layout : Layout fields)
    (written observed : Nat) (writtenIn : written ∈ fields) (observedIn : observed ∈ fields)
    (distinct : written ≠ observed) (index : Fin 4) :
    ¬Native.ByteMemory.Inside (address written).toNat 4 ((address observed).toNat + index.val) := by
  rw [address_toNat written (layout.fits written writtenIn),
    address_toNat observed (layout.fits observed observedIn)]
  have separation := layout.separate written writtenIn observed observedIn distinct
  have below := index.isLt
  unfold Native.ByteMemory.Inside
  omega

theorem translate_destination (instruction : Instruction) (native : State) :
    ByteExecution.destination (translate instruction native) native = address (Machine32.destination instruction) := by
  cases instruction <;> rfl

theorem translate_value (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator) (carry : native.carry = source.carry)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field) :
    ByteExecution.value (translate instruction native) native =
      (Machine32.execute instruction source).memory (Machine32.destination instruction) := by
  cases instruction <;>
    simp_all [dependencies, sources, readField, translate, ByteExecution.value,
      Machine32.execute, Machine32.put, Machine32.destination, write]

theorem translate_accumulator (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field) :
    ByteExecution.accumulator (translate instruction native) native =
      (Machine32.execute instruction source).accumulator := by
  cases instruction <;> try exact accumulator
  exact reads _ (by simp [dependencies, sources, Machine32.destination])

theorem translate_carry (instruction : Instruction) (source : Machine32.State) (native : State)
    (accumulator : native.accumulator = source.accumulator) (carry : native.carry = source.carry)
    (reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field) :
    ByteExecution.carry (translate instruction native) native =
      (Machine32.execute instruction source).carry := by
  cases instruction <;>
    simp_all [dependencies, sources, readField, translate, ByteExecution.carry,
      Machine32.execute, Machine32.put, Machine32.destination]
  rfl

theorem translate_stack (instruction : Instruction) (native : State) :
    (ByteExecution.execute (translate instruction native) native).stack = native.stack := by
  rw [ByteExecution.execute_stack]
  cases instruction <;> rfl

theorem execute_read_destination (instruction : Instruction) (native : State) :
    readField (ByteExecution.execute (translate instruction native) native) (Machine32.destination instruction) =
      ByteExecution.value (translate instruction native) native := by
  unfold readField ByteExecution.prior
  rw [←translate_destination instruction native]
  exact ByteExecution.written_word _ _

theorem execute_read_frame {fields : List Nat} (layout : Layout fields)
    (instruction : Instruction) (native : State) (observed : Nat)
    (writtenIn : Machine32.destination instruction ∈ fields) (observedIn : observed ∈ fields)
    (distinct : observed ≠ Machine32.destination instruction) :
    readField (ByteExecution.execute (translate instruction native) native) observed = readField native observed := by
  unfold readField ByteExecution.prior
  apply ByteExecution.load_frame
  intro index
  rw [translate_destination]
  exact layout_outside layout _ _ writtenIn observedIn (Ne.symm distinct) index

/-- Full finite field-word simulation. The actual four-byte stores preserve
all other represented fields; only initial agreement and static dependencies
are premises. No chosen predicate, mask or resulting native state is supplied. -/
theorem simulate {fields : List Nat} (layout : Layout fields)
    (instruction : Instruction) (source : Machine32.State) (native : State)
    (agreement : Agreement fields source native)
    (included : ∀ field ∈ dependencies instruction, field ∈ fields) :
    Agreement fields (Machine32.execute instruction source)
      (ByteExecution.execute (translate instruction native) native) := by
  have reads : ∀ field ∈ dependencies instruction, readField native field = source.memory field :=
    fun field member => agreement.words field (included field member)
  refine ⟨?_, ?_, ?_⟩
  · rw [ByteExecution.execute_accumulator]
    exact translate_accumulator _ _ _ agreement.accumulator reads
  · rw [ByteExecution.execute_carry]
    exact translate_carry _ _ _ agreement.accumulator agreement.carry reads
  · intro field member
    by_cases equal : field = Machine32.destination instruction
    · subst field
      rw [execute_read_destination]
      exact translate_value _ _ _ agreement.accumulator agreement.carry reads
    · rw [execute_read_frame layout instruction native field
        (included _ (destination_dependency instruction)) member equal,
        Machine32.execute_memory_frame instruction source field equal]
      exact agreement.words field member

@[expose] def run : List Instruction → State → State
  | [], native => native
  | instruction :: rest, native => run rest (ByteExecution.execute (translate instruction native) native)

@[expose] def forms : List Instruction → State → List ByteCode.Form
  | [], _ => []
  | instruction :: rest, native =>
    translate instruction native :: forms rest (ByteExecution.execute (translate instruction native) native)

theorem forms_length (program : List Instruction) (native : State) :
    (forms program native).length = program.length := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih => simp only [forms, List.length_cons, ih]

theorem forms_run (program : List Instruction) (native : State) :
    ByteExecution.run (forms program native) native = run program native := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih => simp only [forms, ByteExecution.run, run, ih]

theorem simulate_run {fields : List Nat} (layout : Layout fields)
    (program : List Instruction) (source : Machine32.State) (native : State)
    (agreement : Agreement fields source native)
    (included : ∀ instruction ∈ program, ∀ field ∈ dependencies instruction, field ∈ fields) :
    Agreement fields (Machine32.run program source) (run program native) := by
  induction program generalizing source native with
  | nil => exact agreement
  | cons instruction rest ih =>
    exact ih _ _ (simulate layout instruction source native agreement
      (included instruction (by simp)))
      (fun next member => included next (by simp [member]))

theorem run_stack (program : List Instruction) (native : State) :
    (run program native).stack = native.stack := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih =>
    exact (ih _).trans (translate_stack instruction native)

theorem run_frame {fields : List Nat} (layout : Layout fields)
    (program : List Instruction) (native : State) (position : Nat)
    (included : ∀ instruction ∈ program, Machine32.destination instruction ∈ fields)
    (outside : ∀ instruction ∈ program,
      ¬Native.ByteMemory.Inside (Machine32.destination instruction) 4 position) :
    (run program native).memory position = native.memory position := by
  induction program generalizing native with
  | nil => rfl
  | cons instruction rest ih =>
    rw [run, ih _ (fun next member => included next (by simp [member]))
      (fun next member => outside next (by simp [member]))]
    apply ByteExecution.execute_frame
    rw [translate_destination, address_toNat _ (layout.fits _ (included instruction (by simp)))]
    exact outside instruction (by simp)

theorem owned_run (owned : Word → Prop) (program : List Instruction) (native : State)
    (ownership : ∀ instruction ∈ program, owned (address (Machine32.destination instruction))) :
    ByteExecution.OwnedRun owned (forms program native) native := by
  induction program generalizing native with
  | nil => trivial
  | cons instruction rest ih =>
    refine ⟨?_, ih _ (fun next member => ownership next (by simp [member]))⟩
    rw [translate_destination]
    exact ownership instruction (by simp)

/-- A supplied ACTUAL live fetch trace refines the source program. Constructing
such a trace from a literal initial image is a separate emitter obligation. -/
theorem trace_refines {fields : List Nat} (layout : Layout fields)
    (program : List Instruction) (source : Machine32.State) (native finish : State)
    (agreement : Agreement fields source native)
    (included : ∀ instruction ∈ program, ∀ field ∈ dependencies instruction, field ∈ fields)
    (trace : ByteExecution.Trace native (forms program native) finish) :
    Agreement fields (Machine32.run program source) finish := by
  rw [ByteExecution.trace_run trace, forms_run]
  exact simulate_run layout program source native agreement included

end SmcTuring.Appendix.FieldRefinement

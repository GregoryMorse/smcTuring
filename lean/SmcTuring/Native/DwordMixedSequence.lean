module
public import SmcTuring.Native.DwordMixedImage

public section
namespace SmcTuring.Native.DwordMixedSequence
abbrev Layout := DwordLayout.Layout

@[expose] def Contiguous (mode : Mode) : Nat → List Layout → Prop
  | _, [] => True
  | start, layout::layouts => layout.start = start ∧ Contiguous mode (DwordLayout.endPC mode layout) layouts
@[expose] def Intact (mode : Mode) (layouts : List Layout) (memory : ByteMemory.Memory) : Prop :=
  ∀ layout ∈ layouts, DwordImage.Intact mode layout memory
@[expose] def OutsideCodes (mode : Mode) (layouts : List Layout) : Prop :=
  ∀ writer ∈ layouts, ∀ reader ∈ layouts,
    writer.destination+4 ≤ reader.start ∨ DwordLayout.endPC mode reader ≤ writer.destination
@[expose] def program (mode : Mode) (layouts : List Layout) : List (MixedDword.Form mode) :=
  layouts.flatMap (fun layout => (DwordLayout.program mode layout).map MixedDword.Form.copy)
@[expose] def finish (mode : Mode) (layouts : List Layout) (state : Execution.State mode) : Execution.State mode :=
  layouts.foldl (fun current layout => DwordEffects.finish mode layout current) state
@[expose] def putFields (memory : ByteMemory.Memory) (layouts : List Layout) (value : BitVec 32) :=
  layouts.foldl (fun current layout => DwordCode.put current layout.destination value) memory

/-- A sequence of helpers uses only its initial images and static layout.
Each helper restores its source before the next helper starts. -/
theorem trace (mode : Mode) (layouts : List Layout) (start : Nat)
    (chain : Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (outside : OutsideCodes mode layouts)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode start)
    (intact : Intact mode layouts state.memory) :
    MixedDword.Trace mode state (program mode layouts) (finish mode layouts state) := by
  induction layouts generalizing start state with
  | nil => exact .nil state
  | cons layout layouts ih =>
    have firstValid := valid layout (List.mem_cons_self ..)
    have location : state.pc = Arithmetic.encodeNat mode layout.start := by rw [chain.1]; exact entry
    have first := DwordMixedImage.trace mode layout firstValid state location
      (intact layout (List.mem_cons_self ..))
    have next : (DwordEffects.finish mode layout state).pc =
        Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      rw [DwordEffects.effect mode layout firstValid state location]
    have restIntact : Intact mode layouts (DwordEffects.finish mode layout state).memory := by
      intro reader member
      rw [DwordEffects.effect mode layout firstValid state location]
      exact DwordImage.intact_put mode reader state.memory
        (intact reader (List.mem_cons_of_mem _ member)) _ _
        (outside layout (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member))
    have rest := ih (DwordLayout.endPC mode layout) chain.2
      (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer member reader readerMember => outside writer (List.mem_cons_of_mem _ member)
        reader (List.mem_cons_of_mem _ readerMember))
      (DwordEffects.finish mode layout state) next restIntact
    simpa only [program,List.flatMap_cons,finish,List.foldl_cons] using
      MixedDword.trace_append mode first rest

theorem endpoint (mode : Mode) (layouts : List Layout) (start : Nat)
    (chain : Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode start) :
    (finish mode layouts state).pc = Arithmetic.encodeNat mode (start+layouts.length*DwordLayout.span mode) := by
  induction layouts generalizing start state with
  | nil => simpa [finish] using entry
  | cons layout layouts ih =>
    have firstValid := valid layout (List.mem_cons_self ..)
    have location : state.pc = Arithmetic.encodeNat mode layout.start := by rw [chain.1]; exact entry
    have next : (DwordEffects.finish mode layout state).pc = Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      rw [DwordEffects.effect mode layout firstValid state location]
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next
    change (finish mode layouts (DwordEffects.finish mode layout state)).pc = _
    rw [rest,DwordLayout.endpoint,chain.1]
    congr 1
    simp [List.length_cons,Nat.add_mul,Nat.add_assoc,Nat.add_comm]

/-- Every layout may read the same mask word. It is restored after each
copy, and all destination writes receive that initial word. -/
theorem memory_effect (mode : Mode) (layouts : List Layout) (start source : Nat)
    (chain : Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (sources : ∀ layout ∈ layouts, layout.source = source)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode start)
    (value : BitVec 32) (mask : DwordCode.get state.memory source = value) :
    (finish mode layouts state).memory = putFields state.memory layouts value := by
  induction layouts generalizing start state with
  | nil => rfl
  | cons layout layouts ih =>
    have firstValid := valid layout (List.mem_cons_self ..)
    have same := sources layout (List.mem_cons_self ..)
    have location : state.pc = Arithmetic.encodeNat mode layout.start := by rw [chain.1]; exact entry
    have next : (DwordEffects.finish mode layout state).pc = Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      rw [DwordEffects.effect mode layout firstValid state location]
    have restored : DwordCode.get (DwordEffects.finish mode layout state).memory source = value := by
      rw [←same,DwordEffects.source_value mode layout firstValid state location,same,mask]
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun reader member => sources reader (List.mem_cons_of_mem _ member)) _ next restored
    change (finish mode layouts (DwordEffects.finish mode layout state)).memory = _
    rw [rest,DwordEffects.effect mode layout firstValid state location,same,mask]
    rfl

@[expose] def bytes (mode : Mode) (layouts : List Layout) := layouts.flatMap (DwordMixedImage.bytes mode)

/-- All initial helper packet images follow from one contiguous group image. -/
theorem intact_of_bytes (mode : Mode) (layouts : List Layout) (start : Nat)
    (chain : Contiguous mode start layouts) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory start (bytes mode layouts).length = bytes mode layouts) :
    Intact mode layouts memory := by
  induction layouts generalizing start with
  | nil => intro layout member; cases member
  | cons layout layouts ih =>
    have firstBytes := ByteWindow.packet memory start [] (DwordMixedImage.bytes mode layout)
      (bytes mode layouts) (by simpa [bytes] using current)
    have first := DwordMixedImage.intact_of_bytes mode layout memory
      (by simpa only [chain.1,List.length_nil,Nat.add_zero] using firstBytes)
    have restBytes := ByteWindow.packet memory start (DwordMixedImage.bytes mode layout)
      (bytes mode layouts) [] (by simpa [bytes,List.append_assoc] using current)
    have position : start+(DwordMixedImage.bytes mode layout).length = DwordLayout.endPC mode layout := by
      rw [DwordMixedImage.bytes_length,DwordLayout.endpoint,chain.1]
    have rest := ih _ chain.2 (by simpa only [position] using restBytes)
    intro reader member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact rest reader member

/-- Destination-only final effects preserve any disjoint complete window. -/
theorem putFields_window (memory : ByteMemory.Memory) (layouts : List Layout) (value : BitVec 32)
    (start count : Nat)
    (outside : ∀ layout ∈ layouts, layout.destination+4 ≤ start ∨ start+count ≤ layout.destination) :
    ByteMemory.bytesAt (putFields memory layouts value) start count = ByteMemory.bytesAt memory start count := by
  induction layouts generalizing memory with
  | nil => rfl
  | cons layout layouts ih =>
    change ByteMemory.bytesAt (putFields (DwordCode.put memory layout.destination value) layouts value) start count = _
    rw [ih _ (fun reader member => outside reader (List.mem_cons_of_mem _ member))]
    exact DwordMixedImage.bytes_frame memory _ _ _ value (outside layout (List.mem_cons_self ..))

/-- Same-field or disjoint-field writes of one value preserve that value. -/
theorem putFields_preserves (memory : ByteMemory.Memory) (layouts : List Layout) (value : BitVec 32)
    (observed : Nat) (initial : DwordCode.get memory observed = value)
    (separate : ∀ writer ∈ layouts, writer.destination = observed ∨
      writer.destination+4 ≤ observed ∨ observed+4 ≤ writer.destination) :
    DwordCode.get (putFields memory layouts value) observed = value := by
  induction layouts generalizing memory with
  | nil => exact initial
  | cons layout layouts ih =>
    change DwordCode.get (putFields (DwordCode.put memory layout.destination value) layouts value) observed = value
    apply ih _ _ (fun writer member => separate writer (List.mem_cons_of_mem _ member))
    rcases separate layout (List.mem_cons_self ..) with same | before | after
    · rw [same,DwordCode.get_put]
    · rw [DwordCode.get_frame _ _ _ _ (by intro index; have bound := index.isLt; simp only [ByteMemory.Inside]; omega)]
      exact initial
    · rw [DwordCode.get_frame _ _ _ _ (by intro index; have bound := index.isLt; simp only [ByteMemory.Inside]; omega)]
      exact initial

theorem putFields_value (memory : ByteMemory.Memory) (layouts : List Layout) (value : BitVec 32)
    (reader : Layout) (member : reader ∈ layouts)
    (separate : ∀ writer ∈ layouts, writer.destination = reader.destination ∨
      writer.destination+4 ≤ reader.destination ∨ reader.destination+4 ≤ writer.destination) :
    DwordCode.get (putFields memory layouts value) reader.destination = value := by
  induction layouts generalizing memory with
  | nil => cases member
  | cons layout layouts ih =>
    change DwordCode.get (putFields (DwordCode.put memory layout.destination value) layouts value) reader.destination = value
    rcases List.mem_cons.mp member with same | member
    · subst reader
      exact putFields_preserves _ _ _ _ (DwordCode.get_put ..)
        (fun writer member => separate writer (List.mem_cons_of_mem _ member))
    · exact ih _ member (fun writer member => separate writer (List.mem_cons_of_mem _ member))

theorem registers (mode : Mode) (layouts : List Layout) (start : Nat)
    (chain : Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode start) :
    (finish mode layouts state).stack = state.stack ∧
    (finish mode layouts state).carry = state.carry ∧
    (finish mode layouts state).accumulator =
      (if layouts.length = 0 then state.accumulator else DwordCode.lift mode (DwordCode.low mode state.accumulator)) := by
  induction layouts generalizing start state with
  | nil => simp [finish]
  | cons layout layouts ih =>
    have firstValid := valid layout (List.mem_cons_self ..)
    have location : state.pc = Arithmetic.encodeNat mode layout.start := by rw [chain.1]; exact entry
    have next : (DwordEffects.finish mode layout state).pc = Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      rw [DwordEffects.effect mode layout firstValid state location]
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next
    rcases rest with ⟨stack,carry,accumulator⟩
    change (finish mode layouts (DwordEffects.finish mode layout state)).stack = _ ∧
      (finish mode layouts (DwordEffects.finish mode layout state)).carry = _ ∧
      (finish mode layouts (DwordEffects.finish mode layout state)).accumulator = _
    rw [stack,carry,accumulator,DwordEffects.effect mode layout firstValid state location]
    simp [DwordCode.low_lift]

end SmcTuring.Native.DwordMixedSequence

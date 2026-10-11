module
public import SmcTuring.Native.StringDwordCopy
public import SmcTuring.Native.DwordMixedSequence

public section
namespace SmcTuring.Native.StringDwordSequence
abbrev Layout := DwordLayout.Layout
abbrev Contiguous := DwordMixedSequence.Contiguous
abbrev Intact := DwordMixedSequence.Intact
abbrev OutsideCodes := DwordMixedSequence.OutsideCodes
@[expose] def program (mode : Mode) (layouts : List Layout) :=
  layouts.flatMap (StringDwordCopy.dwordProgram mode)
@[expose] def finish (mode : Mode) (layouts : List Layout) (state : StringExecution.State mode) :=
  {state with principal := DwordMixedSequence.finish mode layouts state.principal}
@[expose] def SourcesOutside (layouts : List Layout) : Prop :=
  ∀ writer ∈ layouts, ∀ reader ∈ layouts,
    writer.destination+4 ≤ reader.source ∨ reader.source+4 ≤ writer.destination
@[expose] def writes (original : ByteMemory.Memory) : List Layout → ByteMemory.Memory → ByteMemory.Memory
  | [], memory => memory
  | layout::layouts, memory => writes original layouts
      (DwordCode.put memory layout.destination (DwordCode.get original layout.source))

/-- Currentness of each later helper is derived after the preceding copy.
The string decoder uses the canonical overlapping x86 forms. -/
theorem trace (mode : Mode) (layouts : List Layout) (start : Nat)
    (chain : Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (outside : OutsideCodes mode layouts)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (intact : Intact mode layouts state.principal.memory) :
    StringDword.Trace mode state (program mode layouts) (finish mode layouts state) := by
  induction layouts generalizing start state with
  | nil => exact .nil state
  | cons layout layouts ih =>
    have firstValid := valid layout (List.mem_cons_self ..)
    have location : state.principal.pc = Arithmetic.encodeNat mode layout.start := by rw [chain.1];exact entry
    have first := StringDwordCopy.dword_trace mode layout firstValid state location
      (intact layout (List.mem_cons_self ..))
    let nextState := StringDwordCopy.dwordFinish mode layout state
    have next : nextState.principal.pc = Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      change (DwordEffects.finish mode layout state.principal).pc = _
      rw [DwordEffects.effect mode layout firstValid state.principal location]
    have kept : Intact mode layouts nextState.principal.memory := by
      intro reader member
      change DwordImage.Intact mode reader (DwordEffects.finish mode layout state.principal).memory
      rw [DwordEffects.effect mode layout firstValid state.principal location]
      exact DwordImage.intact_put mode reader state.principal.memory
        (intact reader (List.mem_cons_of_mem _ member)) _ _
        (outside layout (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member))
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer member reader readerMember => outside writer (List.mem_cons_of_mem _ member)
        reader (List.mem_cons_of_mem _ readerMember)) nextState next kept
    simpa only [program,List.flatMap_cons,finish,DwordMixedSequence.finish,List.foldl_cons,
      nextState,StringDwordCopy.dwordFinish] using StringDword.trace_append mode first rest

theorem endpoint (mode : Mode) (layouts : List Layout) (start : Nat)
    (chain : Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start) :
    (finish mode layouts state).principal.pc = Arithmetic.encodeNat mode (start+layouts.length*DwordLayout.span mode) :=
  DwordMixedSequence.endpoint mode layouts start chain valid state.principal entry

/-- Different pointer halves are copied from the original memory, rather
than imposing a shared mask value on all source fields. -/
theorem memory_snapshot (mode : Mode) (layouts : List Layout) (start : Nat)
    (chain : Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (outside : SourcesOutside layouts) (original : ByteMemory.Memory)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (values : ∀ reader ∈ layouts, DwordCode.get state.principal.memory reader.source = DwordCode.get original reader.source) :
    (finish mode layouts state).principal.memory = writes original layouts state.principal.memory := by
  induction layouts generalizing start state with
  | nil => rfl
  | cons layout layouts ih =>
    have firstValid := valid layout (List.mem_cons_self ..)
    have location : state.principal.pc = Arithmetic.encodeNat mode layout.start := by rw [chain.1];exact entry
    let nextState := StringDwordCopy.dwordFinish mode layout state
    have effect := DwordEffects.effect mode layout firstValid state.principal location
    have next : nextState.principal.pc = Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      change (DwordEffects.finish mode layout state.principal).pc = _;rw [effect]
    have kept : ∀ reader ∈ layouts,
        DwordCode.get nextState.principal.memory reader.source = DwordCode.get original reader.source := by
      intro reader member
      change DwordCode.get (DwordEffects.finish mode layout state.principal).memory _ = _
      rw [effect,DwordCode.get_frame]
      · exact values reader (List.mem_cons_of_mem _ member)
      · intro index
        have bound := index.isLt
        have apart := outside layout (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member)
        unfold ByteMemory.Inside;omega
    have rest := ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer member reader readerMember => outside writer (List.mem_cons_of_mem _ member)
        reader (List.mem_cons_of_mem _ readerMember)) nextState next kept
    change (finish mode layouts nextState).principal.memory = _
    rw [rest]
    change writes original layouts (DwordEffects.finish mode layout state.principal).memory = _
    rw [effect,values layout (List.mem_cons_self ..)]
    rfl

theorem memory_effect (mode : Mode) (layouts : List Layout) (start : Nat)
    (chain : Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (outside : SourcesOutside layouts) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start) :
    (finish mode layouts state).principal.memory = writes state.principal.memory layouts state.principal.memory :=
  memory_snapshot mode layouts start chain valid outside state.principal.memory state entry (fun _ _ => rfl)

theorem writes_window (original memory : ByteMemory.Memory) (layouts : List Layout) (start count : Nat)
    (outside : ∀ layout ∈ layouts, layout.destination+4 ≤ start ∨ start+count ≤ layout.destination) :
    ByteMemory.bytesAt (writes original layouts memory) start count = ByteMemory.bytesAt memory start count := by
  induction layouts generalizing memory with
  | nil => rfl
  | cons layout layouts ih =>
    change ByteMemory.bytesAt (writes original layouts (DwordCode.put memory layout.destination _)) start count = _
    rw [ih _ (fun reader member => outside reader (List.mem_cons_of_mem _ member))]
    exact DwordMixedImage.bytes_frame memory _ _ _ _ (outside layout (List.mem_cons_self ..))

theorem registers (mode : Mode) (layouts : List Layout) (start : Nat)
    (chain : Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start) :
    (finish mode layouts state).principal.stack = state.principal.stack ∧
    (finish mode layouts state).principal.carry = state.principal.carry ∧
    (finish mode layouts state).principal.accumulator =
      (if layouts.length = 0 then state.principal.accumulator else DwordCode.lift mode (DwordCode.low mode state.principal.accumulator)) ∧
    (finish mode layouts state).sourceIndex = state.sourceIndex ∧
    (finish mode layouts state).destinationIndex = state.destinationIndex ∧
    (finish mode layouts state).backwards = state.backwards := by
  exact ⟨(DwordMixedSequence.registers mode layouts start chain valid state.principal entry).1,
    (DwordMixedSequence.registers mode layouts start chain valid state.principal entry).2.1,
    (DwordMixedSequence.registers mode layouts start chain valid state.principal entry).2.2,rfl,rfl,rfl⟩


/-- Arbitrary distinct-source helpers preserve a disjoint window even when
one destination is a later helper's source. -/
theorem window (mode : Mode) (layouts : List Layout) (start : Nat)
    (chain : Contiguous mode start layouts)
    (valid : ∀ layout ∈ layouts, DwordLayout.Admissible mode layout)
    (state : StringExecution.State mode) (entry : state.principal.pc = Arithmetic.encodeNat mode start)
    (observed count : Nat)
    (outside : ∀ layout ∈ layouts, layout.destination+4 ≤ observed ∨ observed+count ≤ layout.destination) :
    ByteMemory.bytesAt (finish mode layouts state).principal.memory observed count =
      ByteMemory.bytesAt state.principal.memory observed count := by
  induction layouts generalizing start state with
  | nil => rfl
  | cons layout layouts ih =>
    have first := DwordEffects.effect mode layout (valid layout (List.mem_cons_self ..)) state.principal
      (by rw [chain.1];exact entry)
    have next : (StringDwordCopy.dwordFinish mode layout state).principal.pc =
        Arithmetic.encodeNat mode (DwordLayout.endPC mode layout) := by
      change (DwordEffects.finish mode layout state.principal).pc = _
      rw [first]
    change ByteMemory.bytesAt (finish mode layouts (StringDwordCopy.dwordFinish mode layout state)).principal.memory observed count = _
    rw [ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member)) _ next
      (fun reader member => outside reader (List.mem_cons_of_mem _ member))]
    change ByteMemory.bytesAt (DwordEffects.finish mode layout state.principal).memory observed count = _
    rw [first,DwordMixedImage.bytes_frame _ _ _ _ _ (outside layout (List.mem_cons_self ..))]

end SmcTuring.Native.StringDwordSequence

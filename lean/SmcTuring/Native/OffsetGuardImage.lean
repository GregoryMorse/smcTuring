module
public import SmcTuring.Native.SourceData
public import SmcTuring.Native.ReadScalarImage

public section

namespace SmcTuring.Native.OffsetGuardImage

open Execution

/-- The source offset reader and guard share one placement context. Their
caller positions are computed from the emitted read/update sizes. -/
structure Layout (mode : Mode) where
  start : Nat
  readerCallee : Nat
  readerInitial : Word mode
  guard : GuardImage.Layout mode
  offset : Dolan.Mov.Register
  cells : Nat

@[expose] def readLayout (mode : Mode) (layout : Layout mode) : ReadScalarImage.Layout mode :=
  ⟨⟨layout.start, layout.readerCallee, layout.guard.setup.top, layout.guard.setup.slot,
    layout.guard.setup.origin, layout.guard.setup.gridBase, layout.readerInitial, layout.guard.setup.whole⟩,
    layout.guard.setup.candidate⟩
@[expose] def guardLayout (mode : Mode) (layout : Layout mode) : GuardInvocationImage.Layout mode :=
  ⟨ReadScalarImage.endPosition mode .store (readLayout mode layout), layout.guard⟩
@[expose] def guardView (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode (guardLayout mode layout).caller }
@[expose] def afterRead (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  ReadScalarImage.finish mode .store (readLayout mode layout) state
@[expose] def finish (mode : Mode) (layout : Layout mode) (state : State mode) : State mode :=
  GuardInvocationImage.finish mode (guardLayout mode layout) (afterRead mode layout state)
@[expose] def program (mode : Mode) (layout : Layout mode) (state : State mode) : List (Form mode) :=
  ReadScalarImage.program mode .store (readLayout mode layout) state ++
    GuardInvocationImage.program mode (guardLayout mode layout) (afterRead mode layout state)
@[expose] def continuation (mode : Mode) (layout : Layout mode) : Word mode := GuardInvocationImage.callerEnd mode (guardLayout mode layout)

/-- All six final-write fields lie in the control fragment before source data. -/
inductive Field where | candidate | resume | scratch | slot | mask | selected deriving DecidableEq
@[expose] def fieldAddress {mode : Mode} (layout : Layout mode) : Field -> Nat
  | .candidate => layout.guard.setup.candidate
  | .resume => layout.guard.setup.resume
  | .scratch => layout.guard.setup.scratch
  | .slot => layout.guard.setup.slot
  | .mask => layout.guard.mask
  | .selected => layout.guard.selected

/-- Only original-memory setup and physical field separation are supplied.
The executed post-read guard setup and candidate word are derived below. -/
structure Ready (mode : Mode) (layout : Layout mode) (state : State mode) : Prop where
  readSetup : ReadScalarImage.Ready mode .store (readLayout mode layout) state
  guardSetup : GuardInvocationImage.Ready mode (guardLayout mode layout) (guardView mode layout state)
  capacity : SourceData.Capacity mode layout.guard.setup.gridBase layout.cells
  positive : 0 < layout.cells
  fieldsBefore : forall field, fieldAddress layout field < layout.guard.setup.gridBase
  metadataDifferent : forall observed, Not (GuardInvocationImage.metadataWord mode (guardLayout mode layout) observed = Arithmetic.encodeNat mode layout.guard.setup.candidate)
  sourcePointer : load mode state.memory (ReaderImage.label mode layout.readerCallee) =
    SourceData.registerWord mode layout.guard.setup.gridBase layout.offset
  boundary : load mode state.memory (Arithmetic.encodeNat mode layout.guard.setup.boundary) =
    Arithmetic.encodeNat mode (Native.Layout.heapBase mode layout.guard.setup.gridBase)
  sense : layout.guard.sense = .offset

theorem field_fits (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) (field : Field) :
    fieldAddress layout field < 2 ^ (8 * mode.wordBytes) :=
  SourceData.metadata_fits mode layout.guard.setup.gridBase layout.cells _ ready.capacity (ready.fieldsBefore field)

theorem data_not_field (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (above : layout.guard.setup.gridBase <= observed.toNat) (field : Field) :
    Not (observed = Arithmetic.encodeNat mode (fieldAddress layout field)) := by
  intro same
  have values := congrArg (fun value : Word mode => value.toNat) same
  rw [Arithmetic.encode_nat_toNat mode _ (field_fits mode layout state ready field)] at values
  have before := ready.fieldsBefore field
  omega

theorem metadata_after_read (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : GuardInvocationImage.Metadata) :
    load mode (afterRead mode layout state).memory (GuardInvocationImage.metadataWord mode (guardLayout mode layout) observed) =
      load mode state.memory (GuardInvocationImage.metadataWord mode (guardLayout mode layout) observed) :=
  ReadScalarImage.load_frame mode .store (readLayout mode layout) state ready.readSetup _
    (GuardInvocationImage.metadata_owned mode (guardLayout mode layout) _ ready.guardSetup observed)
    (ready.metadataDifferent observed)
    (GuardInvocationImage.metadata_not_slot mode (guardLayout mode layout) _ ready.guardSetup observed)

theorem guard_ready (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    GuardInvocationImage.Ready mode (guardLayout mode layout) (afterRead mode layout state) := by
  apply GuardInvocationImage.transport_ready mode (guardLayout mode layout) _ _ ready.guardSetup
  · exact ReadScalarImage.pc mode .store (readLayout mode layout) state ready.readSetup
  · exact ReadScalarImage.finish_intact mode .store (readLayout mode layout) state ready.readSetup
  · exact metadata_after_read mode layout state ready

theorem read_value (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.guard.setup.gridBase layout.cells source state.memory) :
    ReadScalarImage.readValue mode (readLayout mode layout) state =
      SourceValues.encodeWord mode layout.guard.setup.gridBase (source.registers layout.offset) := by
  rw [ReadScalarImage.read_value_from mode (readLayout mode layout) state _ ready.sourcePointer
    (SourceData.register_not_before mode layout.guard.setup.gridBase layout.cells layout.guard.setup.slot layout.offset ready.capacity
      (field_fits mode layout state ready .slot) (ready.fieldsBefore .slot))]
  exact rep.registers layout.offset

theorem candidate_after_read (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.guard.setup.gridBase layout.cells source state.memory) :
    load mode (afterRead mode layout state).memory (Arithmetic.encodeNat mode layout.guard.setup.candidate) =
      SourceValues.encodeWord mode layout.guard.setup.gridBase (source.registers layout.offset) := by
  have stored := ReadScalarImage.written_value mode .store (readLayout mode layout) state ready.readSetup
  change load mode (afterRead mode layout state).memory (Arithmetic.encodeNat mode layout.guard.setup.candidate) =
    ReadScalarImage.readValue mode (readLayout mode layout) state at stored
  rw [read_value mode layout source state ready rep] at stored
  exact stored

theorem boundary_after_read (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterRead mode layout state).memory (Arithmetic.encodeNat mode layout.guard.setup.boundary) =
      Arithmetic.encodeNat mode (Native.Layout.heapBase mode layout.guard.setup.gridBase) := by
  have frame := metadata_after_read mode layout state ready .boundary
  exact frame.trans ready.boundary

theorem terminal_after_read (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (afterRead mode layout state).memory (Arithmetic.encodeNat mode layout.guard.terminal) =
      load mode state.memory (Arithmetic.encodeNat mode layout.guard.terminal) :=
  metadata_after_read mode layout state ready .terminal

theorem after_read_data_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase observed)
    (above : layout.guard.setup.gridBase <= observed.toNat) :
    load mode (afterRead mode layout state).memory observed = load mode state.memory observed :=
  ReadScalarImage.load_frame mode .store (readLayout mode layout) state ready.readSetup observed owned
    (data_not_field mode layout state ready observed above .candidate) (data_not_field mode layout state ready observed above .slot)

theorem data_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase observed)
    (above : layout.guard.setup.gridBase <= observed.toNat) :
    load mode (finish mode layout state).memory observed = load mode state.memory observed := by
  rw [finish, GuardInvocationImage.load_frame mode (guardLayout mode layout) _ (guard_ready mode layout state ready) observed owned
    (data_not_field mode layout state ready observed above .resume) (data_not_field mode layout state ready observed above .scratch)
    (data_not_field mode layout state ready observed above .slot) (data_not_field mode layout state ready observed above .mask)
    (data_not_field mode layout state ready observed above .selected)]
  exact after_read_data_frame mode layout state ready observed owned above

/-- Read-only metadata outside the six actual scalar writes survives the
whole prefix, including metadata located in the control fragment. -/
theorem load_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (observed : Word mode) (owned : SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase observed)
    (different : forall field, Not (observed = Arithmetic.encodeNat mode (fieldAddress layout field))) :
    load mode (finish mode layout state).memory observed = load mode state.memory observed := by
  rw [finish, GuardInvocationImage.load_frame mode (guardLayout mode layout) _ (guard_ready mode layout state ready) observed owned
    (different .resume) (different .scratch) (different .slot) (different .mask) (different .selected)]
  exact ReadScalarImage.load_frame mode .store (readLayout mode layout) state ready.readSetup observed owned
    (different .candidate) (different .slot)

theorem represented (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.guard.setup.gridBase layout.cells source state.memory) :
    SourceData.Rep mode layout.guard.setup.gridBase layout.cells source (finish mode layout state).memory := by
  constructor
  · intro register
    rw [data_frame mode layout state ready _
      (SourceData.register_owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase layout.cells register ready.capacity)
      (by rw [SourceData.register_toNat mode layout.guard.setup.gridBase layout.cells register ready.capacity]; exact Nat.le_add_right _ _)]
    exact rep.registers register
  · intro pointer inside
    rw [data_frame mode layout state ready _
      (SourceData.heap_owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase layout.cells pointer ready.capacity inside)
      (by rw [SourceData.heap_toNat mode layout.guard.setup.gridBase layout.cells pointer ready.capacity inside]; exact Nat.le_add_right _ _)]
    exact rep.heap pointer inside

/-- Both the accepted and rejected source tag paths execute exactly this
100-instruction current-byte trace before any pointer dereference is attempted. -/
theorem trace (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Fetch.Trace mode state (program mode layout state) (finish mode layout state) :=
  Fetch.trace_append mode (ReadScalarImage.trace mode .store (readLayout mode layout) state ready.readSetup)
    (GuardInvocationImage.trace mode (guardLayout mode layout) _ (guard_ready mode layout state ready))

theorem owned_run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase)
      (program mode layout state) state := by
  have readRun : runForms mode (ReadScalarImage.program mode .store (readLayout mode layout) state) state = afterRead mode layout state :=
    ReadScalarImage.run mode .store (readLayout mode layout) state ready.readSetup
  rw [program, Writes.owned_run_append, readRun]
  exact ⟨ReadScalarImage.owned_run mode .store (readLayout mode layout) state ready.readSetup,
    GuardInvocationImage.owned_run mode (guardLayout mode layout) _ (guard_ready mode layout state ready)⟩

theorem pc (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.guard.setup.gridBase layout.cells source state.memory)
    (inside : match source.registers layout.offset with | .address cell => cell < layout.cells | .offset _ => True) :
    (finish mode layout state).pc = if SourceValues.isOffset (source.registers layout.offset) then continuation mode layout
      else load mode state.memory (Arithmetic.encodeNat mode layout.guard.terminal) := by
  rw [finish, SourceValues.typed_guard_pc mode (guardLayout mode layout) layout.guard.setup.gridBase _ (source.registers layout.offset)
    (guard_ready mode layout state ready) (candidate_after_read mode layout source state ready rep) (boundary_after_read mode layout state ready)
    (SourceData.boundary_fits mode layout.guard.setup.gridBase layout.cells ready.capacity ready.positive)
    (SourceData.value_fits mode layout.guard.setup.gridBase layout.cells (source.registers layout.offset) ready.capacity ready.positive inside)]
  change (if SourceValues.accepts layout.guard.sense (source.registers layout.offset) then continuation mode layout
    else load mode (afterRead mode layout state).memory (Arithmetic.encodeNat mode layout.guard.terminal)) = _
  rw [ready.sense, terminal_after_read mode layout state ready]
  rfl

theorem stack (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).stack = Arithmetic.encodeNat mode layout.guard.setup.slot :=
  GuardInvocationImage.stack mode (guardLayout mode layout) _ (guard_ready mode layout state ready)

theorem carry (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).carry = false := GuardInvocationImage.carry mode (guardLayout mode layout) _ (guard_ready mode layout state ready)

theorem accumulator (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    (finish mode layout state).accumulator = load mode state.memory (Arithmetic.encodeNat mode layout.guard.terminal) := by
  rw [finish, GuardInvocationImage.accumulator mode (guardLayout mode layout) _ (guard_ready mode layout state ready)]
  change (match layout.guard.sense with | .base => _ | .offset => load mode (afterRead mode layout state).memory (Arithmetic.encodeNat mode layout.guard.terminal)) = _
  rw [ready.sense]
  exact terminal_after_read mode layout state ready

theorem finish_intact (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    SpacedCombinedImage.Intact mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase (finish mode layout state).memory :=
  GuardInvocationImage.finish_intact mode (guardLayout mode layout) _ (guard_ready mode layout state ready)

theorem top_reusable (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.guard.setup.top) =
      Arithmetic.encodeNat mode layout.guard.setup.slot + Arithmetic.encodeNat mode mode.wordBytes :=
  GuardInvocationImage.top_reusable mode (guardLayout mode layout) _ (guard_ready mode layout state ready)

theorem selected_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.guard.selected) = (finish mode layout state).pc :=
  GuardInvocationImage.selected_word mode (guardLayout mode layout) _ (guard_ready mode layout state ready)

theorem slot_word (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    load mode (finish mode layout state).memory (Arithmetic.encodeNat mode layout.guard.setup.slot) =
      GuardSelectionImage.callerEnd mode (GuardImage.selectionLayout mode layout.guard) :=
  GuardInvocationImage.slot_word mode (guardLayout mode layout) _ (guard_ready mode layout state ready)

theorem memory_frame (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state)
    (position : Nat) (outside : forall field, Not (ByteMemory.Inside (fieldAddress layout field) mode.wordBytes position)) :
    (finish mode layout state).memory position = state.memory position := by
  rw [finish, GuardInvocationImage.memory_frame mode (guardLayout mode layout) _ (guard_ready mode layout state ready) position
    (outside .resume) (outside .scratch) (outside .slot) (outside .mask) (outside .selected),
    afterRead, ReadScalarImage.memory_frame mode .store (readLayout mode layout) state ready.readSetup position (outside .candidate) (outside .slot)]

theorem run (mode : Mode) (layout : Layout mode) (state : State mode) (ready : Ready mode layout state) :
    runForms mode (program mode layout state) state = finish mode layout state := (Fetch.trace_run_eq mode (trace mode layout state ready)).symm

theorem program_count (mode : Mode) (layout : Layout mode) (state : State mode) : (program mode layout state).length = 100 := by
  simp only [program, List.length_append, ReadScalarImage.program_count, GuardInvocationImage.program_count]

structure Spec (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (start stop : State mode) : Prop where
  represented : SourceData.Rep mode layout.guard.setup.gridBase layout.cells source stop.memory
  trace : Fetch.Trace mode start (program mode layout start) stop
  owned : Writes.OwnedRun mode (SpacedCombinedImage.Owned mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase) (program mode layout start) start
  pc : stop.pc = if SourceValues.isOffset (source.registers layout.offset) then continuation mode layout
    else load mode start.memory (Arithmetic.encodeNat mode layout.guard.terminal)
  intact : SpacedCombinedImage.Intact mode layout.guard.setup.whole layout.guard.setup.origin layout.guard.setup.gridBase stop.memory
  top : load mode stop.memory (Arithmetic.encodeNat mode layout.guard.setup.top) = Arithmetic.encodeNat mode layout.guard.setup.slot + Arithmetic.encodeNat mode mode.wordBytes
  stack : stop.stack = Arithmetic.encodeNat mode layout.guard.setup.slot
  carry : stop.carry = false
  accumulator : stop.accumulator = load mode start.memory (Arithmetic.encodeNat mode layout.guard.terminal)

theorem correct (mode : Mode) (layout : Layout mode) (source : Dolan.Mov.State) (state : State mode)
    (ready : Ready mode layout state) (rep : SourceData.Rep mode layout.guard.setup.gridBase layout.cells source state.memory)
    (inside : match source.registers layout.offset with | .address cell => cell < layout.cells | .offset _ => True) :
    Spec mode layout source state (finish mode layout state) :=
  ⟨represented mode layout source state ready rep, trace mode layout state ready, owned_run mode layout state ready,
    pc mode layout source state ready rep inside, finish_intact mode layout state ready, top_reusable mode layout state ready,
    stack mode layout state ready, carry mode layout state ready, accumulator mode layout state ready⟩

end SmcTuring.Native.OffsetGuardImage

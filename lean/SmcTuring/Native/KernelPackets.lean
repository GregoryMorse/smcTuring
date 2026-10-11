module
public import SmcTuring.Native.KernelImage

public section

namespace SmcTuring.Native.KernelPackets

open ControlImage BlockImage

structure Segment (mode : Mode) where
  start : Nat
  packets : List (Packet mode)

@[expose] def flatten {mode : Mode} (segments : List (Segment mode)) : List (Packet mode) := segments.flatMap Segment.packets
@[expose] def Ordered (mode : Mode) : Nat -> List (Segment mode) -> Nat -> Prop
  | start, [], stop => start = stop
  | start, segment :: rest, stop => segment.start = start ∧
      Ordered mode (segment.start + ControlPacking.size mode segment.packets) rest stop

theorem ordered_size (mode : Mode) (segments : List (Segment mode)) (start stop : Nat)
    (ordered : Ordered mode start segments stop) : start + ControlPacking.size mode (flatten segments) = stop := by
  induction segments generalizing start with
  | nil => exact ordered
  | cons segment rest ih =>
    have tail := ih _ ordered.2
    simpa only [flatten, List.flatMap_cons, Fragment.size_append, ordered.1, Nat.add_assoc] using tail

/-- Every emitted fragment belongs to the computed packet image. No current
memory or fetch condition is needed to establish this static placement. -/
theorem ordered_placement (mode : Mode) (segments : List (Segment mode)) (start stop : Nat)
    (ordered : Ordered mode start segments stop) (segment : Segment mode) (member : segment ∈ segments) :
    Fragment.Within mode (ControlPacking.place mode segment.start segment.packets)
      (ControlPacking.place mode start (flatten segments)) := by
  induction segments generalizing start with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst segment
      simpa only [flatten, List.flatMap_cons, ordered.1] using Fragment.prefix_within mode start first.packets (flatten rest)
    · have embedded := ih _ ordered.2 later
      have suffix := Fragment.suffix_within mode start first.packets (flatten rest)
      rw [ordered.1] at embedded
      exact Fragment.within_trans mode _ _ _ embedded suffix

@[expose] def readCall (mode : Mode) (layout : ReadInvocationImage.Layout mode) : Segment mode :=
  ⟨layout.caller, CallsImage.packets mode layout.caller layout.top (.relative layout.callee)⟩
@[expose] def guardCall (mode : Mode) (layout : GuardInvocationImage.Layout mode) : Segment mode :=
  ⟨layout.caller, CallsImage.packets mode layout.caller layout.guard.setup.top (.relative layout.guard.setup.start)⟩
@[expose] def storeCall (mode : Mode) (layout : StoreInvocationImage.Layout mode) : Segment mode :=
  ⟨layout.caller, CallsImage.packets mode layout.caller layout.top (.relative (StoreInvocationImage.entryPC mode layout))⟩
@[expose] def scalar (mode : Mode) (op : ScalarImage.Op) (layout : ScalarImage.Layout mode) : Segment mode :=
  ⟨layout.start, [.fixed (ScalarImage.form mode op layout)]⟩
@[expose] def readScalar (mode : Mode) (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode) : Segment mode :=
  ⟨layout.reader.caller, (readCall mode layout.reader).packets ++
    (scalar mode op (ReadScalarImage.scalarLayout mode layout)).packets⟩

theorem scalar_size (mode : Mode) (op : ScalarImage.Op) (layout : ScalarImage.Layout mode) :
    ControlPacking.size mode (scalar mode op layout).packets = ScalarImage.size mode op := by
  simp only [scalar, ControlPacking.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Packet.bytes, instruction_length, ScalarImage.form_size, Nat.add_zero]

theorem read_scalar_size (mode : Mode) (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode) :
    layout.reader.caller + ControlPacking.size mode (readScalar mode op layout).packets = ReadScalarImage.endPosition mode op layout := by
  simp only [readScalar, Fragment.size_append, readCall, CallsImage.packet_size, scalar_size,
    ReadScalarImage.endPosition, ReadScalarImage.scalarStart, Nat.add_assoc]

/-- The combined read/update fragment supplies both finer invocation and
scalar placement premises used by the execution proof. -/
theorem read_scalar_placement (mode : Mode) (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode) :
    Fragment.Within mode (ControlPacking.place mode layout.reader.caller (readCall mode layout.reader).packets)
      (ControlPacking.place mode layout.reader.caller (readScalar mode op layout).packets) ∧
    Fragment.Within mode (ControlPacking.place mode (ReadScalarImage.scalarStart mode layout)
      (scalar mode op (ReadScalarImage.scalarLayout mode layout)).packets)
      (ControlPacking.place mode layout.reader.caller (readScalar mode op layout).packets) := by
  exact ⟨Fragment.prefix_within mode _ _ _,
    by simpa only [readScalar, readCall, CallsImage.packet_size, ReadScalarImage.scalarStart] using
      Fragment.suffix_within mode layout.reader.caller (readCall mode layout.reader).packets
        (scalar mode op (ReadScalarImage.scalarLayout mode layout)).packets⟩

@[expose] def addressSegments (mode : Mode) (layout : AddressImage.Layout mode) : List (Segment mode) :=
  [readScalar mode .store (OffsetGuardImage.readLayout mode layout.offset),
    guardCall mode (OffsetGuardImage.guardLayout mode layout.offset),
    readScalar mode .store (PointerImage.baseLayout mode (AddressImage.pointerLayout mode layout)),
    readScalar mode .add (PointerImage.offsetLayout mode (AddressImage.pointerLayout mode layout)),
    readScalar mode .store (PointerImage.wordLayout mode (AddressImage.pointerLayout mode layout)),
    guardCall mode (AddressImage.guardLayout mode layout)]
@[expose] def addressEnd (mode : Mode) (layout : AddressImage.Layout mode) : Nat :=
  (AddressImage.guardLayout mode layout).caller + CallsImage.totalSize mode (.relative layout.guardStart)
@[expose] def segments (mode : Mode) : Block mode -> List (Segment mode)
  | .immediate layout => [readScalar mode .store layout.unit]
  | .load layout => addressSegments mode layout.address ++ [readScalar mode .store (LoadImage.readLayout mode layout)]
  | .store layout => addressSegments mode layout.address ++ [readCall mode (StoreImage.readLayout mode layout), storeCall mode (StoreImage.storeLayout mode layout)]
@[expose] def endPosition (mode : Mode) : Block mode -> Nat
  | .immediate layout => ReadScalarImage.endPosition mode .store layout.unit
  | .load layout => ReadScalarImage.endPosition mode .store (LoadImage.readLayout mode layout)
  | .store layout => (StoreImage.storeLayout mode layout).caller +
      CallsImage.totalSize mode (.relative (StoreInvocationImage.entryPC mode (StoreImage.storeLayout mode layout)))

/-- Every source block has a physically contiguous inline packet sequence;
shared reader/guard bodies are emitted separately and are entered by CALL. -/
theorem source_ordered (mode : Mode) (block : Block mode) :
    Ordered mode (BlockImage.start mode block) (segments mode block) (endPosition mode block) := by
  cases block with
  | immediate layout =>
    exact ⟨rfl, read_scalar_size mode .store layout.unit⟩
  | load layout =>
    simp only [segments, addressSegments, List.cons_append, List.nil_append, Ordered, readScalar, guardCall, Fragment.size_append,
      readCall, CallsImage.packet_size, scalar_size, BlockImage.start, endPosition,
      OffsetGuardImage.readLayout, OffsetGuardImage.guardLayout, ReadScalarImage.endPosition, ReadScalarImage.scalarStart,
      AddressImage.pointerStart, AddressImage.pointerLayout, PointerImage.baseLayout, PointerImage.offsetLayout, PointerImage.wordLayout,
      PointerImage.endPosition, AddressImage.guardLayout, AddressImage.baseGuard, LoadImage.readLayout, LoadImage.readStart,
      Nat.add_assoc]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  | store layout =>
    simp only [segments, addressSegments, List.cons_append, List.nil_append, Ordered, readScalar, guardCall, Fragment.size_append,
      readCall, CallsImage.packet_size, scalar_size, storeCall, BlockImage.start, endPosition,
      OffsetGuardImage.readLayout, OffsetGuardImage.guardLayout, ReadScalarImage.endPosition, ReadScalarImage.scalarStart,
      AddressImage.pointerStart, AddressImage.pointerLayout, PointerImage.baseLayout, PointerImage.offsetLayout, PointerImage.wordLayout,
      PointerImage.endPosition, AddressImage.guardLayout, AddressImage.baseGuard, StoreImage.readLayout, StoreImage.readStart, StoreImage.storeLayout,
      Nat.add_assoc]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem source_continuation (mode : Mode) (block : Block mode) :
    Arithmetic.encodeNat mode (endPosition mode block) = continuation mode block := by
  cases block <;> rfl


theorem ordered_append (mode : Mode) (first second : List (Segment mode)) (start middle stop : Nat)
    (leading : Ordered mode start first middle) (trailing : Ordered mode middle second stop) :
    Ordered mode start (first ++ second) stop := by
  induction first generalizing start with
  | nil =>
    change start = middle at leading
    rw [leading]
    exact trailing
  | cons segment rest ih => exact ⟨leading.1, ih _ leading.2⟩

@[expose] def programSegments (mode : Mode) (blocks : List (Block mode)) : List (Segment mode) := blocks.flatMap (segments mode)

/-- Physical packet contiguity for the actual compiler output. Static no-wrap
bounds turn the compiler's encoded continuations into natural byte positions. -/
theorem program_ordered (mode : Mode) (roles : KernelImage.Roles mode) (start : Nat)
    (source : List Dolan.Mov.Instruction) (blocks : List (Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode roles start source = some (blocks, endPC))
    (startFits : start < 2 ^ (8 * mode.wordBytes))
    (endFits : forall block, block ∈ blocks -> endPosition mode block < 2 ^ (8 * mode.wordBytes)) :
    Ordered mode start (programSegments mode blocks) endPC.toNat := by
  induction source generalizing start blocks endPC with
  | nil =>
    simp only [KernelImage.compile, Option.some.injEq, Prod.mk.injEq] at compiled
    rcases compiled with ⟨rfl, rfl⟩
    change start = (Arithmetic.encodeNat mode start).toNat
    exact (Arithmetic.encode_nat_toNat mode start startFits).symm
  | cons source rest ih =>
    cases first : KernelImage.lower mode roles start source with
    | none => simp only [KernelImage.compile, first, Option.bind_none, reduceCtorEq] at compiled
    | some block =>
      cases tail : KernelImage.compile mode roles (continuation mode block).toNat rest with
      | none => simp only [KernelImage.compile, first, Option.bind_some, tail, Option.map_none, reduceCtorEq] at compiled
      | some result =>
        rcases result with ⟨trailing, trailingEnd⟩
        simp only [KernelImage.compile, first, Option.bind_some, tail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        have fits := endFits block (by simp)
        have next : (continuation mode block).toNat = endPosition mode block := by
          rw [←source_continuation, Arithmetic.encode_nat_toNat mode _ fits]
        have later := ih (continuation mode block).toNat trailing trailingEnd tail
          (by simpa only [next] using fits) (fun observed member => endFits observed (by simp [member]))
        rw [next] at later
        have firstOrdered := source_ordered mode block
        rw [(KernelImage.lower_properties mode roles start source block first).2.1] at firstOrdered
        exact ordered_append mode _ _ _ _ _ firstOrdered later

/-- A source fragment is a member of the whole padded image by construction.
This supplies placement premises for each actual caller/update in the compiler. -/
theorem global_placement (mode : Mode) (roles : KernelImage.Roles mode) (start : Nat)
    (source : List Dolan.Mov.Instruction) (blocks : List (Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode roles start source = some (blocks, endPC))
    (startFits : start < 2 ^ (8 * mode.wordBytes))
    (endFits : forall block, block ∈ blocks -> endPosition mode block < 2 ^ (8 * mode.wordBytes))
    (origin : Nat) (leading trailing : List (SpacedPacking.Piece mode))
    (bodyStart : start = origin + SpacedPacking.size mode leading)
    (block : Block mode) (blockMember : block ∈ blocks) (segment : Segment mode) (segmentMember : segment ∈ segments mode block) :
    Fragment.Within mode (ControlPacking.place mode segment.start segment.packets)
      (SpacedPacking.place mode origin
        (leading ++ SpacedPacking.adjacent mode (flatten (programSegments mode blocks)) ++ trailing)) := by
  have ordered := program_ordered mode roles start source blocks endPC compiled startFits endFits
  have member : segment ∈ programSegments mode blocks := List.mem_flatMap.mpr ⟨block, blockMember, segmentMember⟩
  have localPlacement := ordered_placement mode _ start endPC.toNat ordered segment member
  intro entry belongs
  have placed := localPlacement entry belongs
  rw [bodyStart] at placed
  exact SpacedPacking.adjacent_member mode origin leading trailing _ entry placed


/-- Refining a constructed source segment supplies the exact finer caller and
scalar-entry membership premises, not only the enclosing coarse fragment. -/
theorem global_read_scalar (mode : Mode) (roles : KernelImage.Roles mode) (start : Nat)
    (source : List Dolan.Mov.Instruction) (blocks : List (Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode roles start source = some (blocks, endPC))
    (startFits : start < 2 ^ (8 * mode.wordBytes))
    (endFits : forall block, block ∈ blocks -> endPosition mode block < 2 ^ (8 * mode.wordBytes))
    (origin : Nat) (leading trailing : List (SpacedPacking.Piece mode))
    (bodyStart : start = origin + SpacedPacking.size mode leading)
    (block : Block mode) (blockMember : block ∈ blocks) (op : ScalarImage.Op) (layout : ReadScalarImage.Layout mode)
    (member : readScalar mode op layout ∈ segments mode block) :
    let whole := SpacedPacking.place mode origin
      (leading ++ SpacedPacking.adjacent mode (flatten (programSegments mode blocks)) ++ trailing)
    Fragment.Within mode (ControlPacking.place mode layout.reader.caller (CallsImage.packets mode layout.reader.caller layout.reader.top (.relative layout.reader.callee))) whole ∧
      ScalarImage.entry mode op (ReadScalarImage.scalarLayout mode layout) ∈ whole := by
  have enclosing := global_placement mode roles start source blocks endPC compiled startFits endFits
    origin leading trailing bodyStart block blockMember (readScalar mode op layout) member
  have finer := read_scalar_placement mode op layout
  constructor
  · exact Fragment.within_trans mode _ _ _ finer.1 enclosing
  ·
    apply enclosing
    apply finer.2
    simp only [scalar, ControlPacking.place, ReadScalarImage.scalarLayout, ScalarImage.entry]
    exact List.Mem.head _


@[expose] def headerCount : Dolan.Mov.Instruction -> Nat
  | .immediate _ _ => 4
  | .load _ _ _ => 26
  | .store _ _ _ => 28

theorem source_packet_count (mode : Mode) (block : Block mode) :
    (flatten (segments mode block)).length = headerCount (instruction block) := by
  cases block <;> simp [flatten, segments, addressSegments, readScalar, readCall, guardCall, storeCall, scalar,
    CallsImage.packets, instruction, headerCount]

theorem program_packet_count (mode : Mode) (blocks : List (Block mode)) :
    (flatten (programSegments mode blocks)).length = ((blocks.map instruction).map headerCount).sum := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    change (flatten (segments mode block ++ programSegments mode rest)).length = _
    rw [show flatten (segments mode block ++ programSegments mode rest) =
      flatten (segments mode block) ++ flatten (programSegments mode rest) from List.flatMap_append]
    rw [List.length_append, source_packet_count, ih]
    rfl

/-- The source portion of the exact exported kernel has 1,678 inline packets.
The other 238 fetched-region headers are shared readers, guards and backedge. -/
theorem kernel_packet_count (mode : Mode) (roles : KernelImage.Roles mode) (start : Nat)
    (blocks : List (Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode roles start Dolan.Mov.kernelProgram = some (blocks, endPC)) :
    (flatten (programSegments mode blocks)).length = 1678 := by
  rw [program_packet_count, (KernelImage.compile_properties mode roles start Dolan.Mov.kernelProgram blocks endPC compiled).1]
  decide

end SmcTuring.Native.KernelPackets

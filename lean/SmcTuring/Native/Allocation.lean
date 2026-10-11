module
public import SmcTuring.Native.ProgramLoaded
public import SmcTuring.Native.ReaderBounds
public import SmcTuring.Native.ReadInvocationBounds
public import SmcTuring.Native.ReadScalarBounds
public import SmcTuring.Native.PlacedBounds

public section

namespace SmcTuring.Native.Allocation

open Execution MemoryRegion RegionExecution ControlImage RoleInitialization LayoutPass

/-- One allocation fixed by the emitted code and finite source-grid request.
Its endpoints do not depend on later execution or on an observed trace. -/
@[expose] def region (mode : Mode) (request : Request) : Region :=
  ProgramLoaded.sourceRegion mode request.origin (gridBase mode request) request.cells

theorem origin_before_grid (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) :
    request.origin ≤ gridBase mode request := by
  have bounds := RoleSeparation.position_bounds mode request assembly (.field .top)
  exact Nat.le_trans bounds.1 (Nat.le_of_lt bounds.2)

/-- The complete requested interval fits the finite machine address space. -/
theorem capacity (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) :
    (region mode request).lower ≤ (region mode request).upper ∧
      (region mode request).upper ≤ 2 ^ (8 * mode.wordBytes) :=
  ⟨Nat.le_trans (origin_before_grid mode request assembly) (Nat.le_add_right _ _), assembly.capacity⟩

theorem control_limit (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) :
    request.origin + SpacedPacking.size mode (Assembly.control mode request assembly) = metadataLimit mode request :=
  EmittedImage.whole_extent mode request assembly.reference assembly.blocks assembly.endPC assembly.compiled

/-- Every placed control packet has a conservative fifteen-byte live-fetch window
inside this fixed allocation, including backing bytes after the packet itself. -/
theorem entry_window (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (entry : Entry mode) (member : entry ∈ SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) :
    (region mode request).Contains entry.pc 15 := by
  have lower := SpacedPacking.placed_lower mode _ request.origin entry member
  have upper := SpacedPacking.placed_upper mode _ request.origin entry member
  have limit := control_limit mode request assembly
  have before := BoundedInitialization.metadata_before_grid mode request
  change request.origin ≤ entry.pc ∧ entry.pc + 15 ≤ gridBase mode request + mode.stride * (13 + 2 * request.cells)
  cases mode <;> simp only [Mode.stride, Mode.wordBytes] <;> constructor <;> omega

/-- Placement of a nonempty contiguous fragment supplies its complete span. -/
theorem snippet_bounds (mode : Mode) (whole : List (SpacedPacking.Piece mode)) (origin start : Nat)
    (packets : List (Packet mode)) (nonempty : packets ≠ [])
    (within : Fragment.Within mode (ControlPacking.place mode start packets) (SpacedPacking.place mode origin whole)) :
    origin ≤ start ∧ start + ControlPacking.size mode packets ≤ origin + SpacedPacking.size mode whole :=
  PlacedBounds.snippet_bounds mode whole origin start packets nonempty within

theorem snippet_window (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (start : Nat) (packets : List (Packet mode)) (nonempty : packets ≠ [])
    (within : Fragment.Within mode (ControlPacking.place mode start packets)
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly))) :
    (region mode request).Contains start (ControlPacking.size mode packets + 15) := by
  have bounds := snippet_bounds mode _ request.origin start packets nonempty within
  have limit := control_limit mode request assembly
  have before := BoundedInitialization.metadata_before_grid mode request
  change request.origin ≤ start ∧ start + (ControlPacking.size mode packets + 15) ≤ gridBase mode request + mode.stride * (13 + 2 * request.cells)
  cases mode <;> simp only [Mode.stride, Mode.wordBytes] <;> constructor <;> omega

/-- Every complete constructed metadata/capture/reader operand is contained. -/
theorem operand_contained (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (role : RoleSeparation.Operand) :
    (region mode request).Contains (RoleSeparation.word mode request role).toNat mode.wordBytes := by
  have bounds := RoleSeparation.position_bounds mode request assembly role
  have fits : RoleSeparation.position mode request role < 2 ^ (8 * mode.wordBytes) :=
    Nat.lt_trans bounds.2 (SourceData.base_fits mode _ _ assembly.capacity)
  rw [RoleSeparation.word, Arithmetic.encode_nat_toNat mode _ fits]
  change request.origin ≤ RoleSeparation.position mode request role ∧
    RoleSeparation.position mode request role + mode.wordBytes ≤ gridBase mode request + mode.stride * (13 + 2 * request.cells)
  cases mode <;> simp only [Mode.stride, Mode.wordBytes] <;> constructor <;> omega

theorem register_contained (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (register : Dolan.Mov.Register) :
    (region mode request).Contains (SourceData.registerWord mode (gridBase mode request) register).toNat mode.wordBytes :=
  ProgramLoaded.register_contained mode request.origin _ request.cells
    (origin_before_grid mode request assembly) register assembly.capacity

theorem heap_contained (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (pointer : Nat × Bool) (inside : pointer.1 < request.cells) :
    (region mode request).Contains (SourceData.heapWord mode (gridBase mode request) pointer).toNat mode.wordBytes :=
  ProgramLoaded.heap_contained mode request.origin _ request.cells
    (origin_before_grid mode request assembly) pointer assembly.capacity inside

/-- Each literal shared-reader initial pointer names a complete word within
this allocation, rather than merely belonging to an infinite owner grid. -/
theorem reader_value_contained (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (positive : 0 < request.cells) (role : Reader) :
    (region mode request).Contains (readerValue mode (roleLayout mode request) role).toNat mode.wordBytes := by
  cases role with
  | register register => exact register_contained mode request assembly register
  | candidate => exact operand_contained mode request assembly (.field .candidate)
  | boundary => exact operand_contained mode request assembly (.field .boundary)
  | zero => exact operand_contained mode request assembly (.field .zero)
  | resume => exact operand_contained mode request assembly (.field .resume)
  | terminal => exact operand_contained mode request assembly (.field .terminal)
  | mask => exact operand_contained mode request assembly (.field .mask)
  | offsetZero => exact operand_contained mode request assembly (.field .offsetZero)
  | offsetOne => exact operand_contained mode request assembly (.field .offsetOne)
  | pointerWord => exact operand_contained mode request assembly (.reader .pointer)
  | pointer => exact heap_contained mode request assembly (0, false) positive


/-- All twenty-three shared callee spans and their fetch slack follow from the
constructed pool placement, inside the allocation fixed before execution. -/
theorem reader_window (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (role : Reader) :
    (region mode request).Contains (readerPosition mode (roleLayout mode request) role) (ReadCalleeImage.totalSize mode + 15) := by
  have facts := BoundedInitialization.readers_initialized mode request assembly.toInput (fun _ => 0) role
  have within : Fragment.Within mode (ControlPacking.place mode (readerPosition mode (roleLayout mode request) role)
      (ReadCalleeImage.packets mode (readerPosition mode (roleLayout mode request) role)
        (fieldPosition mode (roleLayout mode request) .top) (fieldPosition mode (roleLayout mode request) .slot)
        (readerValue mode (roleLayout mode request) role)))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)) := facts.within
  have span := snippet_window mode request assembly _ _ (by
    simp [ReadCalleeImage.packets, ReaderImage.packets]) within
  simpa only [ReadCalleeImage.packet_size] using span

/-- Every literal initialized shared-reader caller has a fully derived finite
access certificate in the fixed allocation. Its initial Ready and code/pointer
bounds follow from the actual emitter, not from an assumed future execution. -/
theorem reader_invocation_safe (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (values : Nat → Word mode) (caller : Nat) (role : Reader)
    (within : Fragment.Within mode (ControlPacking.place mode caller (CallsImage.packets mode caller
      (fieldPosition mode (roleLayout mode request) .top) (.relative (readerPosition mode (roleLayout mode request) role))))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)))
    (accumulator stack : Word mode) (carry : Bool) :
    SafeRun mode (region mode request)
      (ReadInvocationImage.program mode (ReadinessAtoms.reader mode request assembly caller role)
        (ReadinessAtoms.state mode request assembly values caller accumulator stack carry))
      (ReadinessAtoms.state mode request assembly values caller accumulator stack carry) := by
  have ready := ReadinessAtoms.reader_ready mode request assembly compact positive values caller role within accumulator stack carry
  have callerCode := snippet_window mode request assembly caller _ (by simp [CallsImage.packets]) within
  rw [CallsImage.packet_size] at callerCode
  have pointer : (region mode request).Contains
      (load mode (ReadinessAtoms.state mode request assembly values caller accumulator stack carry).memory
        (ReaderImage.label mode (readerPosition mode (roleLayout mode request) role))).toNat mode.wordBytes := by
    have initialized := (BoundedInitialization.readers_initialized mode request assembly.toInput values role).initialized
    change load mode (BoundedInitialization.memory mode request assembly.toInput values)
      (ReaderImage.label mode (readerPosition mode (roleLayout mode request) role)) = readerValue mode (roleLayout mode request) role at initialized
    change (region mode request).Contains (load mode (BoundedInitialization.memory mode request assembly.toInput values)
      (ReaderImage.label mode (readerPosition mode (roleLayout mode request) role))).toNat mode.wordBytes
    rw [initialized]
    exact reader_value_contained mode request assembly positive role
  exact ReadInvocationBounds.safe_run mode (region mode request) _ _ ready callerCode
    (reader_window mode request assembly role) (operand_contained mode request assembly (.field .top))
    (operand_contained mode request assembly (.field .slot)) pointer

/-- The complete ten-instruction read round trip executes in the fixed loaded
image, with every observed scalar component and every loaded byte preserved
according to the original read-invocation contract. -/
theorem reader_invocation_loaded (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (values : Nat → Word mode) (caller : Nat) (role : Reader)
    (within : Fragment.Within mode (ControlPacking.place mode caller (CallsImage.packets mode caller
      (fieldPosition mode (roleLayout mode request) .top) (.relative (readerPosition mode (roleLayout mode request) role))))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)))
    (accumulator stack : Word mode) (carry : Bool) :
    let initial := ReadinessAtoms.state mode request assembly values caller accumulator stack carry
    let layout := ReadinessAtoms.reader mode request assembly caller role
    ∃ loadedFinish,
      LoadedExecution.Trace mode (region mode request) (LoadedExecution.snapshot mode (region mode request) initial)
        (ReadInvocationImage.program mode layout initial) loadedFinish ∧
      StateAgree mode (region mode request) (LoadedExecution.expand mode (region mode request) loadedFinish)
        (ReadInvocationImage.finish mode layout initial) :=
  LoadedExecution.trace_complete mode (region mode request)
    (ReadInvocationImage.trace mode _ _ (ReadinessAtoms.reader_ready mode request assembly compact positive values caller role within accumulator stack carry))
    (reader_invocation_safe mode request assembly compact positive values caller role within accumulator stack carry)
    _ (LoadedExecution.snapshot_agrees mode (region mode request) _)


/-- Every typed scalar destination names a complete word in the allocation. -/
theorem destination_contained (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (target : ReadinessAtoms.Destination) :
    (region mode request).Contains (Arithmetic.encodeNat mode (ReadinessAtoms.destination mode request target)).toNat mode.wordBytes := by
  cases target with
  | operand role => exact operand_contained mode request assembly role
  | register reg => exact register_contained mode request assembly reg

/-- A literal placed scalar obtains its fixed-region certificate from the
constructed image and its typed destination. -/
theorem scalar_safe (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (values : Nat → Word mode)
    (start : Nat) (target : ReadinessAtoms.Destination) (op : ScalarImage.Op)
    (member : ScalarImage.entry mode op (ReadinessAtoms.scalar mode request assembly start target) ∈
      SpacedPacking.place mode request.origin (Assembly.control mode request assembly))
    (accumulator stack : Word mode) (carry : Bool) :
    SafeRun mode (region mode request) (ScalarImage.program mode op (ReadinessAtoms.scalar mode request assembly start target))
      (ReadinessAtoms.state mode request assembly values start accumulator stack carry) :=
  ScalarBounds.safe_run mode (region mode request) op _ _
    (ReadinessAtoms.scalar_ready mode request assembly compact values start target op member accumulator stack carry)
    (entry_window mode request assembly _ member) (destination_contained mode request assembly target)

theorem scalar_loaded (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (values : Nat → Word mode)
    (start : Nat) (target : ReadinessAtoms.Destination) (op : ScalarImage.Op)
    (member : ScalarImage.entry mode op (ReadinessAtoms.scalar mode request assembly start target) ∈
      SpacedPacking.place mode request.origin (Assembly.control mode request assembly))
    (accumulator stack : Word mode) (carry : Bool) :
    let initial := ReadinessAtoms.state mode request assembly values start accumulator stack carry
    let layout := ReadinessAtoms.scalar mode request assembly start target
    ∃ loadedFinish,
      LoadedExecution.Trace mode (region mode request) (LoadedExecution.snapshot mode (region mode request) initial)
        (ScalarImage.program mode op layout) loadedFinish ∧
      StateAgree mode (region mode request) (LoadedExecution.expand mode (region mode request) loadedFinish)
        (ScalarImage.finish mode op layout initial) :=
  LoadedExecution.trace_complete mode (region mode request)
    (ScalarImage.trace mode op _ _ (ReadinessAtoms.scalar_ready mode request assembly compact values start target op member accumulator stack carry))
    (scalar_safe mode request assembly compact values start target op member accumulator stack carry)
    _ (LoadedExecution.snapshot_agrees mode (region mode request) _)

/-- The actual eleven-instruction read/update fragment stays in the fixed
allocation. Both finer placements are derived from its literal packet builder. -/
theorem read_scalar_safe (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (values : Nat → Word mode) (caller : Nat) (role : Reader) (target : ReadinessAtoms.Destination) (op : ScalarImage.Op)
    (within : Fragment.Within mode (ControlPacking.place mode caller
      (KernelPackets.readScalar mode op (ReadinessAtoms.update mode request assembly caller role target)).packets)
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)))
    (notSlot : target ≠ .operand (.field .slot)) (notTop : target ≠ .operand (.field .top))
    (accumulator stack : Word mode) (carry : Bool) :
    SafeRun mode (region mode request)
      (ReadScalarImage.program mode op (ReadinessAtoms.update mode request assembly caller role target)
        (ReadinessAtoms.state mode request assembly values caller accumulator stack carry))
      (ReadinessAtoms.state mode request assembly values caller accumulator stack carry) := by
  have finer := KernelPackets.read_scalar_placement mode op (ReadinessAtoms.update mode request assembly caller role target)
  have ready := ReadinessAtoms.read_scalar_ready mode request assembly compact positive values caller role target op within notSlot notTop accumulator stack carry
  have scalarMember : ScalarImage.entry mode op (ReadScalarImage.scalarLayout mode (ReadinessAtoms.update mode request assembly caller role target)) ∈
      SpacedPacking.place mode request.origin (Assembly.control mode request assembly) := by
    apply within; apply finer.2; exact List.Mem.head _
  have readSafe := reader_invocation_safe mode request assembly compact positive values caller role
    (Fragment.within_trans mode _ _ _ finer.1 within) accumulator stack carry
  have scalarSafe := ScalarBounds.safe_run mode (region mode request) op _ _
    (ReadScalarImage.scalar_ready mode op _ _ ready)
    (entry_window mode request assembly _ scalarMember) (destination_contained mode request assembly target)
  apply WindowBounds.safe_run_append mode (region mode request) _ _ _ readSafe
  exact scalarSafe

theorem read_scalar_loaded (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (values : Nat → Word mode) (caller : Nat) (role : Reader) (target : ReadinessAtoms.Destination) (op : ScalarImage.Op)
    (within : Fragment.Within mode (ControlPacking.place mode caller
      (KernelPackets.readScalar mode op (ReadinessAtoms.update mode request assembly caller role target)).packets)
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly)))
    (notSlot : target ≠ .operand (.field .slot)) (notTop : target ≠ .operand (.field .top))
    (accumulator stack : Word mode) (carry : Bool) :
    let initial := ReadinessAtoms.state mode request assembly values caller accumulator stack carry
    let layout := ReadinessAtoms.update mode request assembly caller role target
    ∃ loadedFinish,
      LoadedExecution.Trace mode (region mode request) (LoadedExecution.snapshot mode (region mode request) initial)
        (ReadScalarImage.program mode op layout initial) loadedFinish ∧
      StateAgree mode (region mode request) (LoadedExecution.expand mode (region mode request) loadedFinish)
        (ReadScalarImage.finish mode op layout initial) :=
  LoadedExecution.trace_complete mode (region mode request)
    (ReadScalarImage.trace mode op _ _ (ReadinessAtoms.read_scalar_ready mode request assembly compact positive values caller role target op within notSlot notTop accumulator stack carry))
    (read_scalar_safe mode request assembly compact positive values caller role target op within notSlot notTop accumulator stack carry)
    _ (LoadedExecution.snapshot_agrees mode (region mode request) _)

/-- All control bytes and live-fetch slack lie in the preselected allocation. -/
theorem control_contained (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) :
    PlacedBounds.ControlWithin mode (region mode request) request.origin (Assembly.control mode request assembly) := by
  have limit := control_limit mode request assembly
  have before := BoundedInitialization.metadata_before_grid mode request
  change request.origin ≤ request.origin ∧
    request.origin + (SpacedPacking.size mode (Assembly.control mode request assembly) + 15) ≤
      gridBase mode request + mode.stride * (13 + 2 * request.cells)
  cases mode <;> simp only [Mode.stride, Mode.wordBytes] <;> constructor <;> omega

end SmcTuring.Native.Allocation

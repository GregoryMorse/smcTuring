module
public import SmcTuring.Native.ProgramControl
public import SmcTuring.Native.ProgramEndpoint

public section

namespace SmcTuring.Native.SourceEndpoint

open Execution MemoryRegion RegionExecution LayoutPass MappedExecution RoleInitialization

/-- The unfetched terminal endpoint lies in the host gap when its offset is
strictly smaller than the declared host extent. -/
theorem host_contained (mode : Mode) (request : Request) (inside : request.terminalOffset < request.hostSpan) :
    (Allocation.region mode request).Contains (boundaryStart mode request + request.terminalOffset) 1 := by
  have readers := LayoutPass.reader_extent mode request
  have fields := LayoutPass.field_extent mode request
  have grid := BoundedInitialization.metadata_before_grid mode request
  have order : readerLimit mode request ≤ boundaryStart mode request := by
    simp only [boundaryStart, backedgeStart, kernelStart, offsetGuardStart, baseGuardLimit, baseGuardStart, AlignedPacking.readerStart]
    omega
  change request.origin ≤ boundaryStart mode request + request.terminalOffset ∧
    boundaryStart mode request + request.terminalOffset + 1 ≤ gridBase mode request + mode.stride * (13 + 2 * request.cells)
  change boundaryStart mode request + request.hostSpan + _ = metadataLimit mode request at fields
  constructor <;> omega

theorem backedge_contained (mode : Mode) (request : Request) :
    (Allocation.region mode request).Contains (backedgeStart mode request) 1 := by
  have readers := LayoutPass.reader_extent mode request
  have fields := LayoutPass.field_extent mode request
  have grid := BoundedInitialization.metadata_before_grid mode request
  have order : readerLimit mode request ≤ backedgeStart mode request := by
    simp only [backedgeStart, kernelStart, offsetGuardStart, baseGuardLimit, baseGuardStart, AlignedPacking.readerStart]
    omega
  change request.origin ≤ backedgeStart mode request ∧
    backedgeStart mode request + 1 ≤ gridBase mode request + mode.stride * (13 + 2 * request.cells)
  change backedgeStart mode request + CallsImage.totalSize mode (.indirect 0) + request.hostSpan + _ = metadataLimit mode request at fields
  constructor <;> omega

/-- Containment plus the emitter's capacity turns a natural endpoint into the
same encoded word, then derives configured canonical address validity. -/
theorem contained_word_valid (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (environment : Environment) (mapping : Mapped mode environment (Allocation.region mode request))
    (address : Nat) (contained : (Allocation.region mode request).Contains address 1) :
    AddressSpace.Valid mode environment.paging (Arithmetic.encodeNat mode address).toNat := by
  have capacity := (Allocation.capacity mode request assembly).2
  have upper := contained.2
  have fits : address < 2 ^ (8 * mode.wordBytes) := by omega
  rw [Arithmetic.encode_nat_toNat mode address fits]
  have valid := AddressSpace.contains_valid mode environment.paging (Allocation.region mode request) mapping.fits address 1 contained
    (⟨0, by decide⟩ : Fin 1)
  simpa only [Nat.add_zero] using valid

theorem terminal_word (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool) :
    load mode (Assembly.initial mode request assembly source accumulator stack carry).memory
      (Arithmetic.encodeNat mode (fieldPosition mode (roleLayout mode request) .terminal)) =
      Arithmetic.encodeNat mode (boundaryStart mode request + request.terminalOffset) :=
  (BoundedInitialization.fields_initialized mode request assembly.toInput (SourceData.initialValues mode (gridBase mode request) source) .terminal).initialized

theorem block_snapshot (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) :
    ProgramEndpoint.FailureSnapshot mode (Assembly.initial mode request assembly source accumulator stack carry)
      (LoopInitialization.frozen mode request) (Arithmetic.encodeNat mode (boundaryStart mode request + request.terminalOffset)) block := by
  rcases CompiledLayout.block_lowered mode request assembly block member with ⟨pc, instruction, lowered⟩
  have frozen : LoopInitialization.frozen mode request (Arithmetic.encodeNat mode (fieldPosition mode (roleLayout mode request) .terminal)) :=
    ⟨.field .terminal, trivial, rfl⟩
  have word := terminal_word mode request assembly source accumulator stack carry
  cases instruction with
  | immediate destination value =>
    cases value with
    | address cell => simp only [KernelImage.lower, reduceCtorEq] at lowered
    | offset choice => simp only [KernelImage.lower, Option.some.injEq] at lowered; subst block; trivial
  | load destination base offset =>
    simp only [KernelImage.lower, Option.some.injEq] at lowered
    subst block
    exact ⟨frozen, word⟩
  | store base offset sourceRegister =>
    simp only [KernelImage.lower, Option.some.injEq] at lowered
    subst block
    exact ⟨frozen, word⟩

theorem kernel_pc (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let body := ProgramImage.run mode assembly.blocks source initial
    body.native.pc = if body.accepted then Arithmetic.encodeNat mode (backedgeStart mode request)
      else Arithmetic.encodeNat mode (boundaryStart mode request + request.terminalOffset) :=
  ProgramEndpoint.endpoint mode _ assembly.blocks _ _ _
    (ProgramCertificate.source_setup mode request assembly compact positive source accumulator stack carry) _
    (block_snapshot mode request assembly source accumulator stack carry) assembly.blocks (fun _ member => member) source _
    (Arithmetic.encodeNat mode (backedgeStart mode request))
    (LoopInitialization.initial_invariant mode request assembly positive source accumulator stack carry)
    (ProgramCertificate.entry_word mode request assembly).symm (ProgramCertificate.linked mode request assembly) bounds

theorem kernel_targets (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (environment : Environment) (mapping : Mapped mode environment (Allocation.region mode request))
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (host : request.terminalOffset < request.hostSpan)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let body := ProgramImage.run mode assembly.blocks source initial
    ControlBounds.Targets mode environment body.forms initial := by
  dsimp only
  have endpoint := kernel_pc mode request assembly compact positive source accumulator stack carry bounds
  have valid : AddressSpace.Valid mode environment.paging
      (ProgramImage.run mode assembly.blocks source (Assembly.initial mode request assembly source accumulator stack carry)).native.pc.toNat := by
    rw [endpoint]
    split
    · exact contained_word_valid mode request assembly environment mapping _ (backedge_contained mode request)
    · exact contained_word_valid mode request assembly environment mapping _ (host_contained mode request host)
  exact ControlBounds.targets_of_trace mode environment _ mapping
    (ProgramCertificate.kernel_correct mode request assembly compact positive source accumulator stack carry bounds).trace
    (ProgramAllocation.kernel_safe mode request assembly compact positive source accumulator stack carry bounds) valid

theorem kernel_checked (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (environment : Environment) (mapping : Mapped mode environment (Allocation.region mode request))
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells) (host : request.terminalOffset < request.hostSpan)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let outcome := ProgramImage.run mode assembly.blocks source initial
    let loadedRegion := Allocation.region mode request
    Dolan.Mov.run Dolan.Mov.kernelProgram source = (if outcome.accepted then some outcome.source else none) ∧
      ∃ loadedFinish,
        MappedExecution.Trace mode environment loadedRegion (LoadedExecution.snapshot mode loadedRegion initial) outcome.forms loadedFinish ∧
        StateAgree mode loadedRegion (LoadedExecution.expand mode loadedRegion loadedFinish) outcome.native ∧
        SourceData.Rep mode (gridBase mode request) request.cells outcome.source
          (LoadedExecution.expand mode loadedRegion loadedFinish).memory ∧
        Writes.OwnedRun mode (ProgramImage.owned mode (Assembly.context mode request assembly)) outcome.forms
          (LoadedExecution.expand mode loadedRegion (LoadedExecution.snapshot mode loadedRegion initial)) ∧
        AccessRun mode environment outcome.forms initial ∧
        ControlBounds.Targets mode environment outcome.forms initial ∧
        loadedFinish.pc = if outcome.accepted then Arithmetic.encodeNat mode (backedgeStart mode request)
          else Arithmetic.encodeNat mode (boundaryStart mode request + request.terminalOffset) := by
  dsimp only
  obtain ⟨sourceRun, finish, trace, same, represented, owned, accesses⟩ :=
    ProgramMapped.kernel_checked mode request assembly environment mapping compact positive source accumulator stack carry bounds
  exact ⟨sourceRun, finish, trace, same, represented, owned, accesses,
    kernel_targets mode request assembly environment mapping compact positive host source accumulator stack carry bounds,
    same.1.trans (kernel_pc mode request assembly compact positive source accumulator stack carry bounds)⟩

end SmcTuring.Native.SourceEndpoint

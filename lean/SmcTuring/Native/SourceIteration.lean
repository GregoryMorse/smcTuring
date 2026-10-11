module
public import SmcTuring.Native.SourceChecked
public import SmcTuring.Native.ProgramIteration

public section

namespace SmcTuring.Native.SourceIteration

open Execution MemoryRegion RegionExecution LayoutPass MappedExecution

@[expose] def run (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (count : Nat) (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool) : ProgramImage.Outcome mode :=
  ProgramIteration.run mode (Assembly.context mode request assembly) assembly.blocks (LoopInitialization.loop mode request)
    count source (Assembly.initial mode request assembly source accumulator stack carry)

theorem entry_contained (mode : Mode) (request : Request) :
    (Allocation.region mode request).Contains (kernelStart mode request) 1 := by
  have readers := LayoutPass.reader_extent mode request
  have fields := LayoutPass.field_extent mode request
  have grid := BoundedInitialization.metadata_before_grid mode request
  have order : readerLimit mode request ≤ kernelStart mode request := by
    simp only [kernelStart, offsetGuardStart, baseGuardLimit, baseGuardStart, AlignedPacking.readerStart]
    omega
  change request.origin ≤ kernelStart mode request ∧
    kernelStart mode request + 1 ≤ gridBase mode request + mode.stride * (13 + 2 * request.cells)
  change kernelStart mode request + ByteLengths.programSpan mode Dolan.Mov.kernelProgram +
    CallsImage.totalSize mode (.indirect 0) + request.hostSpan + _ = metadataLimit mode request at fields
  constructor <;> omega

theorem static (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) :
    LoopBounds.Static mode (Allocation.region mode request) (Assembly.context mode request assembly)
      assembly.blocks (LoopInitialization.loop mode request) := {
  blocks := SourceAllocation.block_static mode request assembly
  code := Allocation.control_contained mode request assembly
  top := Allocation.operand_contained mode request assembly (.field .top)
  slot := Allocation.operand_contained mode request assembly (.field .slot)
  target := Allocation.operand_contained mode request assembly (.field .loop) }

/-- One initializer and one fixed allocation suffice for every source-bounded
finite path. The recursive run evolves the same memory through each actual pass. -/
theorem correct (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells) (closed : request.closed = true)
    (count : Nat) (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramIteration.Bounded mode assembly.blocks count source) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    ProgramIteration.Spec mode (Allocation.region mode request) (Assembly.context mode request assembly)
      assembly.blocks (LoopInitialization.loop mode request) initial (LoopInitialization.frozen mode request)
      (LoopInitialization.pointer mode request) (Arithmetic.encodeNat mode (boundaryStart mode request + request.terminalOffset))
      count source initial (run mode request assembly count source accumulator stack carry) := by
  have loopSetup := LoopInitialization.loop_setup mode request assembly compact source accumulator stack carry
  have sameEntry : LoopInitialization.entry mode request =
      ProgramImage.entry mode assembly.blocks (Arithmetic.encodeNat mode (backedgeStart mode request)) := by
    rw [ProgramCertificate.entry_word mode request assembly]
    simp only [LoopInitialization.entry, closed, ite_true]
  rw [sameEntry] at loopSetup
  exact ProgramIteration.correct mode (Allocation.region mode request) _ assembly.blocks _ _ _
    (ProgramCertificate.source_setup mode request assembly compact positive source accumulator stack carry) _
    (SourceEndpoint.block_snapshot mode request assembly source accumulator stack carry)
    assembly.blocks (fun _ member => member) (LoopInitialization.loop mode request) loopSetup (static mode request assembly)
    count source _ (LoopInitialization.initial_invariant mode request assembly positive source accumulator stack carry)
    (ProgramCertificate.entry_word mode request assembly).symm (ProgramCertificate.linked mode request assembly) bounds

/-- The actual entire repeated run has one continuous finite checked execution,
with full source output, code ownership, all modeled checks and exact endpoint.
Every next native state comes from its preceding pass, not a fresh initializer. -/
theorem checked (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (environment : Environment) (mapping : Mapped mode environment (Allocation.region mode request))
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells) (closed : request.closed = true)
    (host : request.terminalOffset < request.hostSpan)
    (count : Nat) (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramIteration.Bounded mode assembly.blocks count source) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let outcome := run mode request assembly count source accumulator stack carry
    let loadedRegion := Allocation.region mode request
    ProgramIteration.sourceRun Dolan.Mov.kernelProgram count source = (if outcome.accepted then some outcome.source else none) ∧
      ∃ loadedFinish,
        CheckedExecution.Trace mode environment loadedRegion (LoadedExecution.snapshot mode loadedRegion initial) outcome.forms loadedFinish ∧
        StateAgree mode loadedRegion (LoadedExecution.expand mode loadedRegion loadedFinish) outcome.native ∧
        SourceData.Rep mode (gridBase mode request) request.cells outcome.source
          (LoadedExecution.expand mode loadedRegion loadedFinish).memory ∧
        Writes.OwnedRun mode (ProgramImage.owned mode (Assembly.context mode request assembly)) outcome.forms
          (LoadedExecution.expand mode loadedRegion (LoadedExecution.snapshot mode loadedRegion initial)) ∧
        AccessRun mode environment outcome.forms initial ∧
        ControlBounds.Targets mode environment outcome.forms initial ∧
        loadedFinish.pc = (if outcome.accepted then Arithmetic.encodeNat mode (kernelStart mode request)
          else Arithmetic.encodeNat mode (boundaryStart mode request + request.terminalOffset)) ∧
        (outcome.accepted = true → 3 * count ≤ outcome.forms.length) := by
  dsimp only
  let initial := Assembly.initial mode request assembly source accumulator stack carry
  let outcome := run mode request assembly count source accumulator stack carry
  let loadedRegion := Allocation.region mode request
  have spec := correct mode request assembly compact positive closed count source accumulator stack carry bounds
  have entryValid : AddressSpace.Valid mode environment.paging
      (ProgramImage.entry mode assembly.blocks (Arithmetic.encodeNat mode (LoopInitialization.loop mode request).start)).toNat := by
    change AddressSpace.Valid mode environment.paging
      (ProgramImage.entry mode assembly.blocks (Arithmetic.encodeNat mode (backedgeStart mode request))).toNat
    rw [ProgramCertificate.entry_word mode request assembly]
    exact SourceEndpoint.contained_word_valid mode request assembly environment mapping _ (entry_contained mode request)
  have terminalValid := SourceEndpoint.contained_word_valid mode request assembly environment mapping _
    (SourceEndpoint.host_contained mode request host)
  have targets := ProgramIteration.targets mode loadedRegion _ assembly.blocks (LoopInitialization.loop mode request)
    initial (LoopInitialization.frozen mode request) (LoopInitialization.pointer mode request) _ count source initial outcome
    spec environment mapping entryValid terminalValid
  have initialSame := LoadedExecution.snapshot_agrees mode loadedRegion initial
  obtain ⟨finish, trace, same⟩ := LoadedExecution.trace_complete mode loadedRegion spec.trace spec.safe _ initialSame
  have checkedTrace := CheckedExecution.trace_complete mode environment loadedRegion mapping trace initial initialSame targets
  refine ⟨?_, finish, checkedTrace, same, ?_, ?_, ?_, targets, ?_, ?_⟩
  · simpa only [(KernelImage.compile_properties mode _ _ _ _ _ assembly.compiled).1] using spec.sourceRun
  · exact ProgramLoaded.represented_agrees mode request.origin (gridBase mode request) request.cells
      (Allocation.origin_before_grid mode request assembly) assembly.capacity outcome.source loadedRegion
      (by exact ⟨Nat.le_refl _, Nat.le_refl _⟩) _ _ same.2.2.2.2 spec.represented
  · exact owned_run_agrees mode loadedRegion _ outcome.forms _ initial initialSame spec.safe spec.owned
  · exact access_run_of_safe mode environment loadedRegion mapping outcome.forms initial spec.safe
  · simpa only [LoadedExecution.expand, LoopInitialization.loop, ProgramCertificate.entry_word mode request assembly] using same.1.trans spec.pc
  · intro accepted
    exact ProgramIteration.accepted_length mode _ _ _ count source initial accepted

end SmcTuring.Native.SourceIteration

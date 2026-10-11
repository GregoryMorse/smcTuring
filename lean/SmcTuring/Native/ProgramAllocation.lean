module
public import SmcTuring.Native.SourceAllocation
public import SmcTuring.Native.ProgramBounds

public section

namespace SmcTuring.Native.ProgramAllocation

open Execution MemoryRegion RegionExecution LayoutPass

/-- Every fetched instruction of the actual emitted source pass accesses only
the allocation chosen before execution. Every block's bounds and current Ready
follow from the emitter and the maintained source invariant. -/
theorem kernel_safe (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    SafeRun mode (Allocation.region mode request) (ProgramImage.run mode assembly.blocks source initial).forms initial :=
  ProgramBounds.safe_run mode (Allocation.region mode request) _ assembly.blocks _ _ _
    (ProgramCertificate.source_setup mode request assembly compact positive source accumulator stack carry)
    (SourceAllocation.block_static mode request assembly)
    assembly.blocks (fun _ member => member) source _ (Arithmetic.encodeNat mode (backedgeStart mode request))
    (LoopInitialization.initial_invariant mode request assembly positive source accumulator stack carry)
    (ProgramCertificate.entry_word mode request assembly).symm (ProgramCertificate.linked mode request assembly) bounds

/-- The accepted pass and actual indirect CALL backedge fit the same prescribed
allocation. The body invariant supplies the current StackTop value. -/
theorem closed_safe (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source)
    (accepted : (ProgramImage.run mode assembly.blocks source (Assembly.initial mode request assembly source accumulator stack carry)).accepted = true) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let body := ProgramImage.run mode assembly.blocks source initial
    SafeRun mode (Allocation.region mode request)
      (body.forms ++ LoopImage.program mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request)) initial := by
  have setup := ProgramCertificate.source_setup mode request assembly compact positive source accumulator stack carry
  have boundary := ProgramImage.successful_boundary mode _ assembly.blocks _ _ _ setup assembly.blocks (fun _ member => member)
    source _ (Arithmetic.encodeNat mode (backedgeStart mode request))
    (LoopInitialization.initial_invariant mode request assembly positive source accumulator stack carry)
    (ProgramCertificate.entry_word mode request assembly).symm (ProgramCertificate.linked mode request assembly) bounds accepted
  have loopSetup := LoopInitialization.loop_setup mode request assembly compact source accumulator stack carry
  have code : PlacedBounds.ControlWithin mode (Allocation.region mode request)
      (Assembly.context mode request assembly).origin (Assembly.context mode request assembly).whole :=
    Allocation.control_contained mode request assembly
  have topValue := (boundary.2.frames _ loopSetup.topFrozen).trans loopSetup.topValue
  have backedgeSafe := PlacedBounds.calls_safe mode (Allocation.region mode request) _ _ _ _ _ _ _ boundary.1
    loopSetup.ranges loopSetup.fits topValue loopSetup.within code
    (Allocation.operand_contained mode request assembly (.field .top))
    (Allocation.operand_contained mode request assembly (.field .slot))
    (Allocation.operand_contained mode request assembly (.field .loop))
  exact PlacedBounds.safe_trace_append mode (Allocation.region mode request)
    (ProgramCertificate.kernel_correct mode request assembly compact positive source accumulator stack carry bounds).trace
    (kernel_safe mode request assembly compact positive source accumulator stack carry bounds) backedgeSafe

theorem kernel_loaded (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let outcome := ProgramImage.run mode assembly.blocks source initial
    let loadedRegion := Allocation.region mode request
    Dolan.Mov.run Dolan.Mov.kernelProgram source = (if outcome.accepted then some outcome.source else none) ∧
      ∃ loadedFinish,
        LoadedExecution.Trace mode loadedRegion (LoadedExecution.snapshot mode loadedRegion initial) outcome.forms loadedFinish ∧
        StateAgree mode loadedRegion (LoadedExecution.expand mode loadedRegion loadedFinish) outcome.native ∧
        SourceData.Rep mode (gridBase mode request) request.cells outcome.source
          (LoadedExecution.expand mode loadedRegion loadedFinish).memory ∧
        Writes.OwnedRun mode (ProgramImage.owned mode (Assembly.context mode request assembly)) outcome.forms
          (LoadedExecution.expand mode loadedRegion (LoadedExecution.snapshot mode loadedRegion initial)) := by
  dsimp only
  let initial := Assembly.initial mode request assembly source accumulator stack carry
  let outcome := ProgramImage.run mode assembly.blocks source initial
  let loadedRegion := Allocation.region mode request
  have kernel := ProgramCertificate.kernel_correct mode request assembly compact positive source accumulator stack carry bounds
  have safe : SafeRun mode loadedRegion outcome.forms initial :=
    kernel_safe mode request assembly compact positive source accumulator stack carry bounds
  have initialSame := LoadedExecution.snapshot_agrees mode loadedRegion initial
  obtain ⟨loadedFinish, trace, same⟩ := LoadedExecution.trace_complete mode loadedRegion kernel.trace safe _ initialSame
  have ordered := RoleSeparation.position_bounds mode request assembly (.field .top)
  have before : request.origin ≤ gridBase mode request := Nat.le_trans ordered.1 (Nat.le_of_lt ordered.2)
  refine ⟨?_, loadedFinish, trace, same, ?_, ?_⟩
  · simpa only [(KernelImage.compile_properties mode _ _ _ _ _ assembly.compiled).1] using kernel.sourceRun
  · exact ProgramLoaded.represented_agrees mode request.origin (gridBase mode request) request.cells before assembly.capacity
      outcome.source loadedRegion (by exact ⟨Nat.le_refl _, Nat.le_refl _⟩) _ _ same.2.2.2.2 kernel.represented
  · exact owned_run_agrees mode loadedRegion _ outcome.forms _ initial initialSame safe kernel.owned


/-- The actual accepted body plus CALL backedge executes in the allocation fixed
by layout and source capacity, returns to entry and retains all finite source data. -/
theorem closed_loaded (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells) (closed : request.closed = true)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source)
    (accepted : (ProgramImage.run mode assembly.blocks source (Assembly.initial mode request assembly source accumulator stack carry)).accepted = true) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let body := ProgramImage.run mode assembly.blocks source initial
    let forms := body.forms ++ LoopImage.program mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request)
    let stop := LoopImage.finish mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request) body.native
    let loadedRegion := Allocation.region mode request
    Dolan.Mov.run Dolan.Mov.kernelProgram source = some body.source ∧
      ∃ loadedFinish,
        LoadedExecution.Trace mode loadedRegion (LoadedExecution.snapshot mode loadedRegion initial) forms loadedFinish ∧
        StateAgree mode loadedRegion (LoadedExecution.expand mode loadedRegion loadedFinish) stop ∧
        SourceData.Rep mode (gridBase mode request) request.cells body.source
          (LoadedExecution.expand mode loadedRegion loadedFinish).memory ∧
        Writes.OwnedRun mode (ProgramImage.owned mode (Assembly.context mode request assembly)) forms
          (LoadedExecution.expand mode loadedRegion (LoadedExecution.snapshot mode loadedRegion initial)) ∧
        loadedFinish.pc = Arithmetic.encodeNat mode (kernelStart mode request) := by
  dsimp only
  let initial := Assembly.initial mode request assembly source accumulator stack carry
  let body := ProgramImage.run mode assembly.blocks source initial
  let forms := body.forms ++ LoopImage.program mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request)
  let loadedRegion := Allocation.region mode request
  have kernel := ProgramCertificate.closed_pass_correct mode request assembly compact positive closed source accumulator stack carry bounds accepted
  have safe : SafeRun mode loadedRegion forms initial :=
    closed_safe mode request assembly compact positive source accumulator stack carry bounds accepted
  have initialSame := LoadedExecution.snapshot_agrees mode loadedRegion initial
  obtain ⟨loadedFinish, trace, same⟩ := LoadedExecution.trace_complete mode loadedRegion kernel.2.1 safe _ initialSame
  have ordered := RoleSeparation.position_bounds mode request assembly (.field .top)
  have before : request.origin ≤ gridBase mode request := Nat.le_trans ordered.1 (Nat.le_of_lt ordered.2)
  refine ⟨kernel.1, loadedFinish, trace, same, ?_, ?_, ?_⟩
  · exact ProgramLoaded.represented_agrees mode request.origin (gridBase mode request) request.cells before assembly.capacity
      body.source loadedRegion (by exact ⟨Nat.le_refl _, Nat.le_refl _⟩) _ _ same.2.2.2.2 kernel.2.2.2.1.represented
  · exact owned_run_agrees mode loadedRegion _ forms _ initial initialSame safe kernel.2.2.1
  · exact same.1.trans kernel.2.2.2.2

end SmcTuring.Native.ProgramAllocation

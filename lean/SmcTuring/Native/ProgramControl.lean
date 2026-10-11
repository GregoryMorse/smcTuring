module
public import SmcTuring.Native.ProgramMapped
public import SmcTuring.Native.ControlBounds

public section

namespace SmcTuring.Native.ProgramControl

open Execution MemoryRegion RegionExecution LayoutPass MappedExecution

/-- Every direct and indirect CALL of an accepted closed pass has a valid target,
including the final backedge. Its endpoint equals the contained initial entry. -/
theorem closed_targets (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (environment : Environment) (mapping : Mapped mode environment (Allocation.region mode request))
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells) (closed : request.closed = true)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source)
    (accepted : (ProgramImage.run mode assembly.blocks source (Assembly.initial mode request assembly source accumulator stack carry)).accepted = true) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let body := ProgramImage.run mode assembly.blocks source initial
    let forms := body.forms ++ LoopImage.program mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request)
    ControlBounds.Targets mode environment forms initial := by
  dsimp only
  have checked := ProgramCertificate.closed_pass_correct mode request assembly compact positive closed source accumulator stack carry bounds accepted
  have safe := ProgramAllocation.closed_safe mode request assembly compact positive source accumulator stack carry bounds accepted
  have nonempty : (ProgramImage.run mode assembly.blocks source (Assembly.initial mode request assembly source accumulator stack carry)).forms ++
      LoopImage.program mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request) ≠ [] := by
    intro impossible
    have count := congrArg List.length impossible
    simp only [LoopImage.program, Calls.program, List.length_append, List.length_cons, List.length_nil] at count
    omega
  have initialValid := ControlBounds.pc_valid_of_safe mode environment _ mapping _ _ nonempty safe
  have finishValid : AddressSpace.Valid mode environment.paging
      (LoopImage.finish mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request)
        (ProgramImage.run mode assembly.blocks source (Assembly.initial mode request assembly source accumulator stack carry)).native).pc.toNat := by
    rw [checked.2.2.2.2]
    exact initialValid
  exact ControlBounds.targets_of_trace mode environment _ mapping checked.2.1 safe finishValid

theorem closed_checked (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (environment : Environment) (mapping : Mapped mode environment (Allocation.region mode request))
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
        MappedExecution.Trace mode environment loadedRegion (LoadedExecution.snapshot mode loadedRegion initial) forms loadedFinish ∧
        StateAgree mode loadedRegion (LoadedExecution.expand mode loadedRegion loadedFinish) stop ∧
        SourceData.Rep mode (gridBase mode request) request.cells body.source
          (LoadedExecution.expand mode loadedRegion loadedFinish).memory ∧
        Writes.OwnedRun mode (ProgramImage.owned mode (Assembly.context mode request assembly)) forms
          (LoadedExecution.expand mode loadedRegion (LoadedExecution.snapshot mode loadedRegion initial)) ∧
        loadedFinish.pc = Arithmetic.encodeNat mode (kernelStart mode request) ∧
        AccessRun mode environment forms initial ∧
        ControlBounds.Targets mode environment forms initial := by
  dsimp only
  obtain ⟨sourceRun, finish, trace, same, represented, owned, pc, accesses⟩ :=
    ProgramMapped.closed_checked mode request assembly environment mapping compact positive closed source accumulator stack carry bounds accepted
  exact ⟨sourceRun, finish, trace, same, represented, owned, pc, accesses,
    closed_targets mode request assembly environment mapping compact positive closed source accumulator stack carry bounds accepted⟩

end SmcTuring.Native.ProgramControl

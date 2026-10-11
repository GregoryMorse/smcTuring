module
public import SmcTuring.Native.SourceEndpoint
public import SmcTuring.Native.CheckedExecution

public section

namespace SmcTuring.Native.SourceChecked

open Execution MemoryRegion RegionExecution LayoutPass MappedExecution

theorem kernel (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (environment : Environment) (mapping : Mapped mode environment (Allocation.region mode request))
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells) (host : request.terminalOffset < request.hostSpan)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let outcome := ProgramImage.run mode assembly.blocks source initial
    let loadedRegion := Allocation.region mode request
    Dolan.Mov.run Dolan.Mov.kernelProgram source = (if outcome.accepted then some outcome.source else none) ∧
      ∃ loadedFinish,
        CheckedExecution.Trace mode environment loadedRegion (LoadedExecution.snapshot mode loadedRegion initial) outcome.forms loadedFinish ∧
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
  obtain ⟨sourceRun, finish, trace, same, represented, owned, accesses, targets, pc⟩ :=
    SourceEndpoint.kernel_checked mode request assembly environment mapping compact positive host source accumulator stack carry bounds
  have checked := CheckedExecution.trace_complete mode environment _ mapping (MappedExecution.trace_loaded mode environment _ trace)
    (Assembly.initial mode request assembly source accumulator stack carry)
    (LoadedExecution.snapshot_agrees mode _ _) targets
  exact ⟨sourceRun, finish, checked, same, represented, owned, accesses, targets, pc⟩

theorem closed (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
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
        CheckedExecution.Trace mode environment loadedRegion (LoadedExecution.snapshot mode loadedRegion initial) forms loadedFinish ∧
        StateAgree mode loadedRegion (LoadedExecution.expand mode loadedRegion loadedFinish) stop ∧
        SourceData.Rep mode (gridBase mode request) request.cells body.source
          (LoadedExecution.expand mode loadedRegion loadedFinish).memory ∧
        Writes.OwnedRun mode (ProgramImage.owned mode (Assembly.context mode request assembly)) forms
          (LoadedExecution.expand mode loadedRegion (LoadedExecution.snapshot mode loadedRegion initial)) ∧
        loadedFinish.pc = Arithmetic.encodeNat mode (kernelStart mode request) ∧
        AccessRun mode environment forms initial ∧
        ControlBounds.Targets mode environment forms initial := by
  dsimp only
  obtain ⟨sourceRun, finish, trace, same, represented, owned, pc, accesses, targets⟩ :=
    ProgramControl.closed_checked mode request assembly environment mapping compact positive closed source accumulator stack carry bounds accepted
  have checked := CheckedExecution.trace_complete mode environment _ mapping (MappedExecution.trace_loaded mode environment _ trace)
    (Assembly.initial mode request assembly source accumulator stack carry)
    (LoadedExecution.snapshot_agrees mode _ _) targets
  exact ⟨sourceRun, finish, checked, same, represented, owned, pc, accesses, targets⟩

end SmcTuring.Native.SourceChecked

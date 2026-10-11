module
public import SmcTuring.Native.ProgramAllocation
public import SmcTuring.Native.MappedExecution

public section

namespace SmcTuring.Native.ProgramMapped

open Execution MemoryRegion RegionExecution LayoutPass MappedExecution

/-- Effective RWX permissions on every byte of the fixed allocation. This is
an environment precondition, not a claim that an OS maps arbitrary intervals. -/
@[expose] def RWX (environment : Environment) (region : Region) : Prop :=
  ∀ address, region.lower ≤ address → address < region.upper →
    environment.readable address = true ∧ environment.writable address = true ∧ environment.executable address = true

theorem mapped (mode : Mode) (request : Request) (environment : Environment)
    (fits : AddressSpace.Fits mode environment.paging (Allocation.region mode request))
    (permissions : RWX environment (Allocation.region mode request)) :
    Mapped mode environment (Allocation.region mode request) :=
  ⟨fits, fun address lower upper => (permissions address lower upper).1,
    fun address lower upper => (permissions address lower upper).2.1,
    fun address lower upper => (permissions address lower upper).2.2⟩

/-- Finite x86 capacity already gives address validity for flat segments. -/
theorem x86_mapped (request : Request) (assembly : Assembly.Image .x86 request) (environment : Environment)
    (permissions : RWX environment (Allocation.region .x86 request)) :
    Mapped .x86 environment (Allocation.region .x86 request) :=
  mapped .x86 request environment (AddressSpace.x86_fits _ _ (by simpa only [Mode.wordBytes] using (Allocation.capacity .x86 request assembly).2)) permissions

theorem x64_low_mapped (request : Request) (environment : Environment)
    (upper : (Allocation.region .x64 request).upper ≤ AddressSpace.half environment.paging)
    (permissions : RWX environment (Allocation.region .x64 request)) :
    Mapped .x64 environment (Allocation.region .x64 request) :=
  mapped .x64 request environment (AddressSpace.x64_low_fits _ _ upper) permissions

theorem x64_high_mapped (request : Request) (assembly : Assembly.Image .x64 request) (environment : Environment)
    (lower : AddressSpace.highStart environment.paging ≤ (Allocation.region .x64 request).lower)
    (permissions : RWX environment (Allocation.region .x64 request)) :
    Mapped .x64 environment (Allocation.region .x64 request) :=
  mapped .x64 request environment (AddressSpace.x64_high_fits _ _ lower (by simpa only [Mode.wordBytes] using (Allocation.capacity .x64 request assembly).2)) permissions

theorem kernel_checked (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (environment : Environment) (mapping : Mapped mode environment (Allocation.region mode request))
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
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
        AccessRun mode environment outcome.forms initial := by
  dsimp only
  obtain ⟨sourceRun, finish, trace, same, represented, owned⟩ :=
    ProgramAllocation.kernel_loaded mode request assembly compact positive source accumulator stack carry bounds
  exact ⟨sourceRun, finish, MappedExecution.trace_complete mode environment _ mapping trace, same, represented, owned,
    access_run_of_safe mode environment _ mapping _ _
      (ProgramAllocation.kernel_safe mode request assembly compact positive source accumulator stack carry bounds)⟩

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
        AccessRun mode environment forms initial := by
  dsimp only
  obtain ⟨sourceRun, finish, trace, same, represented, owned, pc⟩ :=
    ProgramAllocation.closed_loaded mode request assembly compact positive closed source accumulator stack carry bounds accepted
  exact ⟨sourceRun, finish, MappedExecution.trace_complete mode environment _ mapping trace, same, represented, owned, pc,
    access_run_of_safe mode environment _ mapping _ _
      (ProgramAllocation.closed_safe mode request assembly compact positive source accumulator stack carry bounds accepted)⟩

end SmcTuring.Native.ProgramMapped

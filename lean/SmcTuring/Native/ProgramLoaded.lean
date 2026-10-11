module
public import SmcTuring.Native.FiniteFootprint
public import SmcTuring.Native.ProgramCertificate

public section

namespace SmcTuring.Native.ProgramLoaded

open Execution MemoryRegion RegionExecution LayoutPass

/-- Include the complete represented finite register/heap grid as well as all
control bytes from the image's origin. This permits full finite output recovery,
including source cells that the particular pass did not access. -/
@[expose] def sourceRegion (mode : Mode) (origin base cells : Nat) : Region :=
  ⟨origin, base + mode.stride * (13 + 2 * cells)⟩

theorem register_contained (mode : Mode) (origin base cells : Nat) (before : origin ≤ base)
    (register : Dolan.Mov.Register) (capacity : SourceData.Capacity mode base cells) :
    (sourceRegion mode origin base cells).Contains (SourceData.registerWord mode base register).toNat mode.wordBytes := by
  rw [SourceData.register_toNat mode base cells register capacity]
  have small := (Dolan.Four.slot register).isLt
  cases mode <;> simp only [sourceRegion, Region.Contains, SourceData.registerAddress,
    Layout.registerField, Layout.fieldAddress, Mode.stride, Mode.wordBytes] <;> constructor <;> omega

theorem heap_contained (mode : Mode) (origin base cells : Nat) (before : origin ≤ base)
    (pointer : Nat × Bool) (capacity : SourceData.Capacity mode base cells) (inside : pointer.1 < cells) :
    (sourceRegion mode origin base cells).Contains (SourceData.heapWord mode base pointer).toNat mode.wordBytes := by
  rw [SourceData.heap_toNat mode base cells pointer capacity inside]
  cases mode <;> cases second : pointer.2 <;> simp [sourceRegion, Region.Contains, SourceData.heapAddress,
    Layout.heapField, Layout.fieldAddress, Mode.stride, Mode.wordBytes, second] <;> constructor <;> omega

/-- The complete represented finite source output transfers through byte agreement,
not through a new assumption that the finite machine already represents it. -/
theorem represented_agrees (mode : Mode) (origin base cells : Nat) (before : origin ≤ base)
    (capacity : SourceData.Capacity mode base cells) (source : Dolan.Mov.State)
    (region : Region) (includes : FiniteFootprint.Widens (sourceRegion mode origin base cells) region)
    (left right : ByteMemory.Memory) (same : Agree region left right)
    (rep : SourceData.Rep mode base cells source right) : SourceData.Rep mode base cells source left := {
  registers := fun register => (load_agree mode region same _
    (FiniteFootprint.contains_widen includes _ _ (register_contained mode origin base cells before register capacity))).trans
      (rep.registers register)
  heap := fun pointer inside => (load_agree mode region same _
    (FiniteFootprint.contains_widen includes _ _ (heap_contained mode origin base cells before pointer capacity inside))).trans
      (rep.heap pointer inside) }

@[expose] def region (mode : Mode) (request : Request) (forms : List (Form mode)) (initial : State mode) : Region :=
  FiniteFootprint.join (FiniteFootprint.run mode forms initial)
    (sourceRegion mode request.origin (gridBase mode request) request.cells)

/-- A real whole-kernel pass is realized by a constructed finite loaded state,
with the literal source outcome, full finite source output and code-owned writes.
The extent is computed from the actual accesses and the represented grid;
containment in a prescribed mapped/canonical hardware allocation remains separate. -/
theorem kernel_prefix (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let outcome := ProgramImage.run mode assembly.blocks source initial
    let loadedRegion := region mode request outcome.forms initial
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
  let loadedRegion := region mode request outcome.forms initial
  have kernel := ProgramCertificate.kernel_correct mode request assembly compact positive source accumulator stack carry bounds
  have safe : SafeRun mode loadedRegion outcome.forms initial :=
    FiniteFootprint.safe_run_widen mode (FiniteFootprint.join_left _ _) _ _ (FiniteFootprint.run_safe mode _ _)
  have initialSame := LoadedExecution.snapshot_agrees mode loadedRegion initial
  obtain ⟨loadedFinish, trace, same⟩ := LoadedExecution.trace_complete mode loadedRegion kernel.trace safe _ initialSame
  have ordered := RoleSeparation.position_bounds mode request assembly (.field .top)
  have before : request.origin ≤ gridBase mode request := Nat.le_trans ordered.1 (Nat.le_of_lt ordered.2)
  refine ⟨?_, loadedFinish, trace, same, ?_, ?_⟩
  · simpa only [(KernelImage.compile_properties mode _ _ _ _ _ assembly.compiled).1] using kernel.sourceRun
  · exact represented_agrees mode request.origin (gridBase mode request) request.cells before assembly.capacity
      outcome.source loadedRegion (FiniteFootprint.join_right _ _) _ _ same.2.2.2.2 kernel.represented
  · exact owned_run_agrees mode loadedRegion _ outcome.forms _ initial initialSame safe kernel.owned


/-- The actual accepted body plus CALL backedge also has a finite loaded
execution, returns to kernel entry and retains all represented finite source data. -/
theorem closed_prefix (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells) (closed : request.closed = true)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source)
    (accepted : (ProgramImage.run mode assembly.blocks source (Assembly.initial mode request assembly source accumulator stack carry)).accepted = true) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let body := ProgramImage.run mode assembly.blocks source initial
    let forms := body.forms ++ LoopImage.program mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request)
    let stop := LoopImage.finish mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request) body.native
    let loadedRegion := region mode request forms initial
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
  let loadedRegion := region mode request forms initial
  have kernel := ProgramCertificate.closed_pass_correct mode request assembly compact positive closed source accumulator stack carry bounds accepted
  have safe : SafeRun mode loadedRegion forms initial :=
    FiniteFootprint.safe_run_widen mode (FiniteFootprint.join_left _ _) _ _ (FiniteFootprint.run_safe mode _ _)
  have initialSame := LoadedExecution.snapshot_agrees mode loadedRegion initial
  obtain ⟨loadedFinish, trace, same⟩ := LoadedExecution.trace_complete mode loadedRegion kernel.2.1 safe _ initialSame
  have ordered := RoleSeparation.position_bounds mode request assembly (.field .top)
  have before : request.origin ≤ gridBase mode request := Nat.le_trans ordered.1 (Nat.le_of_lt ordered.2)
  refine ⟨kernel.1, loadedFinish, trace, same, ?_, ?_, ?_⟩
  · exact represented_agrees mode request.origin (gridBase mode request) request.cells before assembly.capacity
      body.source loadedRegion (FiniteFootprint.join_right _ _) _ _ same.2.2.2.2 kernel.2.2.2.1.represented
  · exact owned_run_agrees mode loadedRegion _ forms _ initial initialSame safe kernel.2.2.1
  · exact same.1.trans kernel.2.2.2.2

end SmcTuring.Native.ProgramLoaded

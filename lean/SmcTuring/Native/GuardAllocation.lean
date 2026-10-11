module
public import SmcTuring.Native.Allocation
public import SmcTuring.Native.GuardInvocationBounds

public section

namespace SmcTuring.Native.GuardAllocation

open Execution MemoryRegion RegionExecution ControlImage RoleInitialization LayoutPass

private theorem code_contained (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (sense : GuardImage.Sense) :
    PlacedBounds.ControlWithin mode (Allocation.region mode request)
      (GuardPlacement.guard mode request assembly sense).setup.origin (GuardPlacement.guard mode request assembly sense).setup.whole := by
  change PlacedBounds.ControlWithin mode (Allocation.region mode request) request.origin assembly.reference
  rw [assembly.consistent]
  exact Allocation.control_contained mode request assembly

/-- Both actual initialized guard orientations execute entirely in the fixed
allocation, with no assumed safe trace or supplied intermediate setup. -/
theorem safe_run (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (values : Nat → Word mode) (accumulator stack : Word mode) (carry : Bool) (sense : GuardImage.Sense) :
    let layout := GuardPlacement.guard mode request assembly sense
    let initial := ReadinessAtoms.state mode request assembly values layout.setup.start accumulator stack carry
    SafeRun mode (Allocation.region mode request) (GuardImage.program mode layout initial) initial :=
  GuardBounds.safe_run mode (Allocation.region mode request) _ _
    (GuardReadiness.guard_ready mode request assembly compact positive values accumulator stack carry sense)
    (code_contained mode request assembly sense)
    (Allocation.operand_contained mode request assembly (.field .top))
    (Allocation.operand_contained mode request assembly (.field .slot))
    (Allocation.operand_contained mode request assembly (.field .resume))
    (Allocation.operand_contained mode request assembly (.field .scratch))
    (Allocation.operand_contained mode request assembly (.field .candidate))
    (Allocation.operand_contained mode request assembly (.field .boundary))
    (Allocation.operand_contained mode request assembly (.field .zero))
    (Allocation.operand_contained mode request assembly (.field .mask))
    (Allocation.operand_contained mode request assembly (.field .selected))
    (Allocation.operand_contained mode request assembly (.field .terminal))

theorem loaded (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (values : Nat → Word mode) (accumulator stack : Word mode) (carry : Bool) (sense : GuardImage.Sense) :
    let layout := GuardPlacement.guard mode request assembly sense
    let initial := ReadinessAtoms.state mode request assembly values layout.setup.start accumulator stack carry
    ∃ loadedFinish,
      LoadedExecution.Trace mode (Allocation.region mode request) (LoadedExecution.snapshot mode (Allocation.region mode request) initial)
        (GuardImage.program mode layout initial) loadedFinish ∧
      StateAgree mode (Allocation.region mode request) (LoadedExecution.expand mode (Allocation.region mode request) loadedFinish)
        (GuardImage.finish mode layout initial) :=
  LoadedExecution.trace_complete mode (Allocation.region mode request)
    (GuardImage.trace mode _ _ (GuardReadiness.guard_ready mode request assembly compact positive values accumulator stack carry sense))
    (safe_run mode request assembly compact positive values accumulator stack carry sense)
    _ (LoadedExecution.snapshot_agrees mode (Allocation.region mode request) _)

/-- A literal placed outer caller and its complete guard execute in the
prescribed allocation; the original initialized memory derives all readiness. -/
theorem invocation_safe (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (values : Nat → Word mode) (accumulator stack : Word mode) (carry : Bool) (sense : GuardImage.Sense)
    (caller : Nat)
    (within : Fragment.Within mode (ControlPacking.place mode caller (CallsImage.packets mode caller
      (fieldPosition mode (roleLayout mode request) .top) (.relative (GuardPlacement.guard mode request assembly sense).setup.start)))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly))) :
    let layout : GuardInvocationImage.Layout mode := ⟨caller, GuardPlacement.guard mode request assembly sense⟩
    let initial := ReadinessAtoms.state mode request assembly values caller accumulator stack carry
    SafeRun mode (Allocation.region mode request) (GuardInvocationImage.program mode layout initial) initial :=
  GuardInvocationBounds.safe_run mode (Allocation.region mode request) _ _
    (InvocationReadiness.guard_for mode request assembly compact positive values accumulator stack carry sense caller within)
    (code_contained mode request assembly sense)
    (Allocation.operand_contained mode request assembly (.field .top))
    (Allocation.operand_contained mode request assembly (.field .slot))
    (Allocation.operand_contained mode request assembly (.field .resume))
    (Allocation.operand_contained mode request assembly (.field .scratch))
    (Allocation.operand_contained mode request assembly (.field .candidate))
    (Allocation.operand_contained mode request assembly (.field .boundary))
    (Allocation.operand_contained mode request assembly (.field .zero))
    (Allocation.operand_contained mode request assembly (.field .mask))
    (Allocation.operand_contained mode request assembly (.field .selected))
    (Allocation.operand_contained mode request assembly (.field .terminal))

theorem invocation_loaded (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (values : Nat → Word mode) (accumulator stack : Word mode) (carry : Bool) (sense : GuardImage.Sense)
    (caller : Nat)
    (within : Fragment.Within mode (ControlPacking.place mode caller (CallsImage.packets mode caller
      (fieldPosition mode (roleLayout mode request) .top) (.relative (GuardPlacement.guard mode request assembly sense).setup.start)))
      (SpacedPacking.place mode request.origin (Assembly.control mode request assembly))) :
    let layout : GuardInvocationImage.Layout mode := ⟨caller, GuardPlacement.guard mode request assembly sense⟩
    let initial := ReadinessAtoms.state mode request assembly values caller accumulator stack carry
    ∃ loadedFinish,
      LoadedExecution.Trace mode (Allocation.region mode request) (LoadedExecution.snapshot mode (Allocation.region mode request) initial)
        (GuardInvocationImage.program mode layout initial) loadedFinish ∧
      StateAgree mode (Allocation.region mode request) (LoadedExecution.expand mode (Allocation.region mode request) loadedFinish)
        (GuardInvocationImage.finish mode layout initial) :=
  LoadedExecution.trace_complete mode (Allocation.region mode request)
    (GuardInvocationImage.trace mode _ _ (InvocationReadiness.guard_for mode request assembly compact positive values accumulator stack carry sense caller within))
    (invocation_safe mode request assembly compact positive values accumulator stack carry sense caller within)
    _ (LoadedExecution.snapshot_agrees mode (Allocation.region mode request) _)

end SmcTuring.Native.GuardAllocation

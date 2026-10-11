module
public import SmcTuring.Native.Allocation
public import SmcTuring.Native.BlockBounds

public section

namespace SmcTuring.Native.SourceAllocation

open Execution MemoryRegion RegionExecution ControlImage RoleInitialization LayoutPass

/-- The complete represented source grid lies inside the fixed allocation. -/
theorem data_within (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) :
    SourceAccess.DataWithin mode (Allocation.region mode request) (gridBase mode request) request.cells :=
  ⟨Allocation.register_contained mode request assembly, Allocation.heap_contained mode request assembly⟩

/-- Every source guard metadata word is an actual contained emitted operand. -/
theorem guard_fields (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) (sense : GuardImage.Sense) :
    SourceAccess.GuardFields mode (Allocation.region mode request) (GuardPlacement.guard mode request assembly sense) :=
  ⟨Allocation.operand_contained mode request assembly (.field .top),
    Allocation.operand_contained mode request assembly (.field .slot),
    Allocation.operand_contained mode request assembly (.field .resume),
    Allocation.operand_contained mode request assembly (.field .scratch),
    Allocation.operand_contained mode request assembly (.field .candidate),
    Allocation.operand_contained mode request assembly (.field .boundary),
    Allocation.operand_contained mode request assembly (.field .zero),
    Allocation.operand_contained mode request assembly (.field .mask),
    Allocation.operand_contained mode request assembly (.field .selected),
    Allocation.operand_contained mode request assembly (.field .terminal)⟩

/-- Every actual compiled source block's allocation certificate is constructed
from its literal lowerer witness and the requested allocation, without any
executed state, future pointer or access certificate as a premise. -/
theorem block_static (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) :
    BlockBounds.StaticBounds mode (Allocation.region mode request) block := by
  rcases CompiledLayout.block_lowered mode request assembly block member with ⟨pc, instruction, lowered⟩
  have common := (KernelImage.lower_properties mode (roles mode request assembly.reference) pc instruction block lowered).2.2
  refine {
    code := ?_
    data := ?_
    top := ?_
    slot := ?_
    operands := ?_ }
  · rw [common]
    change PlacedBounds.ControlWithin mode (Allocation.region mode request) request.origin assembly.reference
    rw [assembly.consistent]
    exact Allocation.control_contained mode request assembly
  · rw [common]
    exact data_within mode request assembly
  · rw [common]
    exact Allocation.operand_contained mode request assembly (.field .top)
  · rw [common]
    exact Allocation.operand_contained mode request assembly (.field .slot)
  · cases instruction with
    | immediate destination value =>
      cases value with
      | address cell => simp only [KernelImage.lower, reduceCtorEq] at lowered
      | offset choice =>
        simp only [KernelImage.lower, Option.some.injEq] at lowered
        subst block
        cases choice with
        | false => exact Allocation.operand_contained mode request assembly (.field .offsetZero)
        | true => exact Allocation.operand_contained mode request assembly (.field .offsetOne)
    | load destination base offset =>
      simp only [KernelImage.lower, Option.some.injEq] at lowered
      subst block
      exact ⟨guard_fields mode request assembly .offset, Allocation.operand_contained mode request assembly (.reader .pointer)⟩
    | store base offset source =>
      simp only [KernelImage.lower, Option.some.injEq] at lowered
      subst block
      exact ⟨guard_fields mode request assembly .offset, Allocation.operand_contained mode request assembly (.reader .pointer)⟩

/-- A compiled block's actual current readiness, cell bounds and represented
source state suffice; all allocation bounds are derived from the emitter. -/
theorem block_safe (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) (source : Dolan.Mov.State) (state : State mode)
    (ready : BlockImage.Ready mode block state) (bounds : BlockImage.Bounds mode block source)
    (rep : BlockImage.Rep mode block source state) :
    SafeRun mode (Allocation.region mode request) (BlockImage.program mode block source state) state :=
  BlockBounds.safe_run mode (Allocation.region mode request) block source state ready bounds rep (block_static mode request assembly block member)

theorem block_loaded (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) (source : Dolan.Mov.State) (state : State mode)
    (ready : BlockImage.Ready mode block state) (bounds : BlockImage.Bounds mode block source)
    (rep : BlockImage.Rep mode block source state) :
    ∃ loadedFinish,
      LoadedExecution.Trace mode (Allocation.region mode request) (LoadedExecution.snapshot mode (Allocation.region mode request) state)
        (BlockImage.program mode block source state) loadedFinish ∧
      StateAgree mode (Allocation.region mode request) (LoadedExecution.expand mode (Allocation.region mode request) loadedFinish)
        (BlockImage.finish mode block source state) :=
  BlockBounds.loaded mode (Allocation.region mode request) block source state ready bounds rep (block_static mode request assembly block member)

end SmcTuring.Native.SourceAllocation

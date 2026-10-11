module
public import SmcTuring.Native.SourceReadiness

public section

namespace SmcTuring.Native.ProgramCertificate

open ControlImage RoleInitialization LayoutPass

/-- The single active pointer operand has the same layout in every load and
store. Immediate destination writes cannot alias it. -/
theorem pointer_layout (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (block : BlockImage.Block mode) (member : block ∈ assembly.blocks) :
    match block with
    | .immediate _ => Not (BlockImage.MayWrite mode block (Arithmetic.encodeNat mode (LoopInitialization.pointer mode request)))
    | .load layout => Arithmetic.encodeNat mode (LoopInitialization.pointer mode request) = ReaderImage.label mode layout.address.pointerCallee
    | .store layout => Arithmetic.encodeNat mode (LoopInitialization.pointer mode request) = ReaderImage.label mode layout.address.pointerCallee := by
  rcases CompiledLayout.block_lowered mode request assembly block member with ⟨pc, instruction, lowered⟩
  cases instruction with
  | immediate destination value =>
    cases value with
    | address cell => simp only [KernelImage.lower, reduceCtorEq] at lowered
    | offset choice =>
      simp only [KernelImage.lower, Option.some.injEq] at lowered
      subst block
      rintro (slot | register)
      · exact RoleSeparation.reader_field_different mode request assembly .pointer .slot slot
      · exact SourceData.register_not_before mode (gridBase mode request) request.cells (LoopInitialization.pointer mode request)
          destination assembly.capacity (RoleSeparation.position_fits mode request assembly (.reader .pointer))
          (RoleSeparation.position_bounds mode request assembly (.reader .pointer)).2 register.symm
  | load destination base offset =>
    simp only [KernelImage.lower, Option.some.injEq] at lowered
    subst block; rfl
  | store base offset source =>
    simp only [KernelImage.lower, Option.some.injEq] at lowered
    subst block; rfl

/-- Complete emitter-derived static source-schedule setup. Every field follows
from actual compilation, placement and initialization. No original or future
Ready, trace, represented result or simulation conclusion is supplied. -/
theorem source_setup (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool) :
    ProgramImage.Setup mode (Assembly.context mode request assembly) assembly.blocks
      (Assembly.initial mode request assembly source accumulator stack carry)
      (LoopInitialization.frozen mode request) (LoopInitialization.pointer mode request) := {
  common := Assembly.common_context mode request assembly
  initialReady := SourceReadiness.block_ready mode request assembly compact positive
    (SourceData.initialValues mode (gridBase mode request) source) accumulator stack carry
  staticFrozen := CompiledLayout.static_frozen mode request assembly
  frozenOwned := LoopInitialization.frozen_owned mode request assembly
  frozenOutside := CompiledLayout.frozen_outside mode request assembly
  capacity := assembly.capacity
  topBefore := BoundedInitialization.field_before_grid mode request .top
  slotBefore := BoundedInitialization.field_before_grid mode request .slot
  pointerOwned := BoundedInitialization.reader_owned mode request assembly.toInput .pointer
  pointerLayout := fun block member => by cases block <;> exact pointer_layout mode request assembly _ member }

theorem end_word (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) :
    assembly.endPC = Arithmetic.encodeNat mode (backedgeStart mode request) := by
  have encoded := congrArg (Arithmetic.encodeNat mode) (Assembly.compiled_bounds mode request assembly).1
  simpa only [Arithmetic.encodeNat, BitVec.ofNat_toNat, BitVec.setWidth_eq] using encoded

theorem entry_word (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) :
    ProgramImage.entry mode assembly.blocks (Arithmetic.encodeNat mode (backedgeStart mode request)) = Arithmetic.encodeNat mode (kernelStart mode request) := by
  have entry := (KernelImage.compile_properties mode _ _ _ _ _ assembly.compiled).2.1
  rw [end_word] at entry
  exact entry

theorem linked (mode : Mode) (request : Request) (assembly : Assembly.Image mode request) :
    ProgramImage.Linked mode assembly.blocks (Arithmetic.encodeNat mode (backedgeStart mode request)) := by
  have connected := (KernelImage.compile_properties mode _ _ _ _ _ assembly.compiled).2.2.1
  rw [end_word] at connected
  exact connected

/-- One full bounded native kernel pass is a fetched code-owned execution of
the literal source schedule, with exact source outcome and representation.
Only capacity, compactness and the path's source-address bounds are required. -/
theorem kernel_correct (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source) :
    ProgramImage.Spec mode (Assembly.context mode request assembly) assembly.blocks source
      (Assembly.initial mode request assembly source accumulator stack carry)
      (ProgramImage.run mode assembly.blocks source (Assembly.initial mode request assembly source accumulator stack carry)) :=
  ProgramImage.correct mode _ assembly.blocks _ _ _ (source_setup mode request assembly compact positive source accumulator stack carry)
    assembly.blocks (fun _ member => member) source _ (Arithmetic.encodeNat mode (backedgeStart mode request))
    (LoopInitialization.initial_invariant mode request assembly positive source accumulator stack carry)
    (entry_word mode request assembly).symm (linked mode request assembly) bounds

/-- An accepted closed native pass executes the real backedge, returns to the
computed kernel entry and restores the complete reusable invariant. -/
theorem closed_pass_correct (mode : Mode) (request : Request) (assembly : Assembly.Image mode request)
    (compact : ReadinessAtoms.Compact mode request) (positive : 0 < request.cells) (closed : request.closed = true)
    (source : Dolan.Mov.State) (accumulator stack : Word mode) (carry : Bool)
    (bounds : ProgramImage.Bounded mode assembly.blocks source)
    (accepted : (ProgramImage.run mode assembly.blocks source (Assembly.initial mode request assembly source accumulator stack carry)).accepted = true) :
    let initial := Assembly.initial mode request assembly source accumulator stack carry
    let body := ProgramImage.run mode assembly.blocks source initial
    let stop := LoopImage.finish mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request) body.native
    Dolan.Mov.run Dolan.Mov.kernelProgram source = some body.source ∧
      Fetch.Trace mode initial (body.forms ++ LoopImage.program mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request)) stop ∧
      Writes.OwnedRun mode (ProgramImage.owned mode (Assembly.context mode request assembly))
        (body.forms ++ LoopImage.program mode (Assembly.context mode request assembly) (LoopInitialization.loop mode request)) initial ∧
      ProgramImage.Invariant mode (Assembly.context mode request assembly) initial
        (LoopInitialization.frozen mode request) (LoopInitialization.pointer mode request) body.source stop ∧
      stop.pc = Arithmetic.encodeNat mode (kernelStart mode request) := by
  have loopSetup := LoopInitialization.loop_setup mode request assembly compact source accumulator stack carry
  have sameEntry : LoopInitialization.entry mode request =
      ProgramImage.entry mode assembly.blocks (Arithmetic.encodeNat mode (backedgeStart mode request)) := by
    rw [entry_word]
    simp only [LoopInitialization.entry, closed, ite_true]
  rw [sameEntry] at loopSetup
  have checked := LoopImage.pass_correct mode _ assembly.blocks _ _ _
    (source_setup mode request assembly compact positive source accumulator stack carry) assembly.blocks (fun _ member => member)
    (LoopInitialization.loop mode request) loopSetup source _
    (LoopInitialization.initial_invariant mode request assembly positive source accumulator stack carry)
    (entry_word mode request assembly).symm (linked mode request assembly) bounds accepted
  simpa only [(KernelImage.compile_properties mode _ _ _ _ _ assembly.compiled).1, LoopInitialization.loop, entry_word mode request assembly] using checked

end SmcTuring.Native.ProgramCertificate

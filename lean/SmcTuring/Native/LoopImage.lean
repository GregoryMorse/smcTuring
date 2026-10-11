module
public import SmcTuring.Native.ProgramImage

public section

namespace SmcTuring.Native.LoopImage

open Execution BlockImage ProgramImage

structure Layout where
  start : Nat
  target : Nat

@[expose] def transfer (layout : Layout) : CallsImage.Transfer := .indirect layout.target
@[expose] def program (mode : Mode) (ctx : Context mode) (layout : Layout) : List (Form mode) :=
  Calls.program mode (CallsImage.firstDisp mode layout.start ctx.top) (CallsImage.secondDisp mode layout.start ctx.top)
    (CallsImage.callTarget mode layout.start (transfer layout))
@[expose] def finish (mode : Mode) (ctx : Context mode) (layout : Layout) (state : State mode) : State mode :=
  Calls.called mode state (CallsImage.firstDisp mode layout.start ctx.top) (CallsImage.secondDisp mode layout.start ctx.top)
    (CallsImage.callTarget mode layout.start (transfer layout))

/-- Static placement and initial code-word values for the backedge. Both
StackTop and the target remain in the finite preserved metadata set. -/
structure Setup (mode : Mode) (ctx : Context mode) (layout : Layout) (initial : State mode)
    (frozen : Word mode -> Prop) (pointer : Nat) (entryPC : Word mode) : Prop where
  ranges : CallsImage.Ranges mode layout.start ctx.top (transfer layout)
  fits : layout.start + CallsImage.totalSize mode (transfer layout) < 2 ^ (8 * mode.wordBytes)
  enough : moffsOperandOffset mode <= ctx.gridBase
  gap : ctx.origin + SpacedPacking.size mode ctx.whole <= ctx.gridBase - moffsOperandOffset mode
  within : Fragment.Within mode (ControlPacking.place mode layout.start (CallsImage.packets mode layout.start ctx.top (transfer layout)))
    (SpacedPacking.place mode ctx.origin ctx.whole)
  topOwned : ProgramImage.owned mode ctx (Arithmetic.encodeNat mode ctx.top)
  slotOwned : ProgramImage.owned mode ctx (Arithmetic.encodeNat mode ctx.slot)
  topFrozen : frozen (Arithmetic.encodeNat mode ctx.top)
  targetFrozen : frozen (Arithmetic.encodeNat mode layout.target)
  topValue : load mode initial.memory (Arithmetic.encodeNat mode ctx.top) =
    Arithmetic.encodeNat mode ctx.slot + Arithmetic.encodeNat mode mode.wordBytes
  targetValue : load mode initial.memory (Arithmetic.encodeNat mode layout.target) = entryPC
  pointerNotSlot : Not (Arithmetic.encodeNat mode pointer = Arithmetic.encodeNat mode ctx.slot)
  frozenNotSlot : forall word, frozen word -> Not (word = Arithmetic.encodeNat mode ctx.slot)

structure Spec (mode : Mode) (ctx : Context mode) (layout : Layout) (initial : State mode)
    (frozen : Word mode -> Prop) (pointer : Nat) (source : Dolan.Mov.State) (state stop : State mode) (entryPC : Word mode) : Prop where
  trace : Fetch.Trace mode state (program mode ctx layout) stop
  owned : Writes.OwnedRun mode (ProgramImage.owned mode ctx) (program mode ctx layout) state
  invariant : Invariant mode ctx initial frozen pointer source stop
  pc : stop.pc = entryPC
  stack : stop.stack = Arithmetic.encodeNat mode ctx.slot
  accumulator : stop.accumulator = state.accumulator
  carry : stop.carry = state.carry

/-- The literal two-instruction reset and indirect CALL write their return
into code, restore reusable metadata, and return to the source program entry. -/
theorem correct (mode : Mode) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode -> Prop) (pointer : Nat)
    (sourceSetup : ProgramImage.Setup mode ctx schedule initial frozen pointer)
    (layout : Layout) (entryPC : Word mode) (setup : Setup mode ctx layout initial frozen pointer entryPC)
    (source : Dolan.Mov.State) (state : State mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = Arithmetic.encodeNat mode layout.start) :
    Spec mode ctx layout initial frozen pointer source state (finish mode ctx layout state) entryPC := by
  have topValue := (inv.frames _ setup.topFrozen).trans setup.topValue
  have targetValue := (inv.frames _ setup.targetFrozen).trans setup.targetValue
  have stackReady := CallsImage.stack_ready mode layout.start ctx.top ctx.slot (transfer layout) state location setup.ranges topValue
  have trace := CallsImage.trace mode layout.start ctx.top ctx.origin ctx.gridBase (transfer layout) ctx.whole state
    location setup.ranges setup.fits setup.enough setup.gap setup.within inv.intact setup.topOwned
  have ownerRun := CallsImage.owned_run mode layout.start ctx.top ctx.slot ctx.origin ctx.gridBase (transfer layout) ctx.whole state
    location setup.ranges topValue setup.topOwned setup.slotOwned
  have frame : forall word, ProgramImage.owned mode ctx word -> Not (word = Arithmetic.encodeNat mode ctx.slot) ->
      load mode (finish mode ctx layout state).memory word = load mode state.memory word := by
    intro word owner different
    rw [finish, Calls.called_memory mode state _ _ _ _ _ stackReady]
    exact Writes.load_frame mode state.memory _ _ _ (Fragment.owned_fields_separate mode ctx.whole ctx.origin ctx.gridBase
      _ _ setup.gap owner setup.slotOwned different)
  have slotFits := SourceData.metadata_fits mode ctx.gridBase ctx.cells ctx.slot sourceSetup.capacity sourceSetup.slotBefore
  have dataRep : ProgramImage.represented mode ctx source (finish mode ctx layout state) := by
    constructor
    · intro register
      rw [frame _ (SourceData.register_owned mode ctx.whole ctx.origin ctx.gridBase ctx.cells register sourceSetup.capacity)
        (SourceData.register_not_before mode ctx.gridBase ctx.cells ctx.slot register sourceSetup.capacity slotFits sourceSetup.slotBefore)]
      exact inv.represented.registers register
    · intro position inside
      rw [frame _ (SourceData.heap_owned mode ctx.whole ctx.origin ctx.gridBase ctx.cells position sourceSetup.capacity inside)
        (SourceData.heap_not_before mode ctx.gridBase ctx.cells ctx.slot position sourceSetup.capacity inside slotFits sourceSetup.slotBefore)]
      exact inv.represented.heap position inside
  have resultFrames : frames mode frozen initial (finish mode ctx layout state) := by
    intro word observed
    exact (frame word (sourceSetup.frozenOwned word observed) (setup.frozenNotSlot word observed)).trans (inv.frames word observed)
  have resultSelected : selected mode ctx pointer (finish mode ctx layout state) := by
    rcases inv.selected with ⟨position, inside, points⟩
    exact ⟨position, inside, (frame _ sourceSetup.pointerOwned setup.pointerNotSlot).trans points⟩
  have resultIntact : ProgramImage.intact mode ctx (finish mode ctx layout state) :=
    SpacedCombinedImage.trace_intact mode ctx.whole ctx.origin ctx.gridBase state _ _ setup.enough setup.gap inv.intact ownerRun trace
  have resultPC := CallsImage.target_pc mode layout.start ctx.top (transfer layout) state location setup.ranges
  exact ⟨trace, ownerRun, ⟨dataRep, resultIntact, resultFrames, resultSelected⟩,
    resultPC.trans targetValue, Calls.called_stack mode state _ _ _ _ _ stackReady,
    Calls.called_accumulator mode state _ _ _, Calls.called_carry mode state _ _ _⟩

/-- A complete successful source pass followed by its actual native backedge.
This theorem composes byte fetch, purity and reuse with literal source run. -/
theorem pass_correct (mode : Mode) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode -> Prop) (pointer : Nat)
    (sourceSetup : ProgramImage.Setup mode ctx schedule initial frozen pointer)
    (blocks : List (Block mode)) (included : forall block, block ∈ blocks -> block ∈ schedule)
    (layout : Layout) (loopSetup : Setup mode ctx layout initial frozen pointer (entry mode blocks (Arithmetic.encodeNat mode layout.start)))
    (source : Dolan.Mov.State) (state : State mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = entry mode blocks (Arithmetic.encodeNat mode layout.start))
    (linked : Linked mode blocks (Arithmetic.encodeNat mode layout.start)) (bounds : Bounded mode blocks source)
    (accepted : (run mode blocks source state).accepted = true) :
    let body := run mode blocks source state
    let stop := finish mode ctx layout body.native
    Dolan.Mov.run (blocks.map instruction) source = some body.source ∧
      Fetch.Trace mode state (body.forms ++ program mode ctx layout) stop ∧
      Writes.OwnedRun mode (ProgramImage.owned mode ctx) (body.forms ++ program mode ctx layout) state ∧
      Invariant mode ctx initial frozen pointer body.source stop ∧
      stop.pc = entry mode blocks (Arithmetic.encodeNat mode layout.start) := by
  have bodyChecked := ProgramImage.correct mode ctx schedule initial frozen pointer sourceSetup blocks included source state _ inv location linked bounds
  have boundary := successful_boundary mode ctx schedule initial frozen pointer sourceSetup blocks included source state _ inv location linked bounds accepted
  have loopChecked := correct mode ctx schedule initial frozen pointer sourceSetup layout _ loopSetup _ _ boundary.2 boundary.1
  have formsOwned : Writes.OwnedRun mode (ProgramImage.owned mode ctx)
      ((run mode blocks source state).forms ++ program mode ctx layout) state := by
    rw [Writes.owned_run_append, ←Fetch.trace_run_eq mode bodyChecked.trace]
    exact ⟨bodyChecked.owned, loopChecked.owned⟩
  exact ⟨by simpa [accepted] using bodyChecked.sourceRun, Fetch.trace_append mode bodyChecked.trace loopChecked.trace,
    formsOwned, loopChecked.invariant, loopChecked.pc⟩

end SmcTuring.Native.LoopImage

module
public import SmcTuring.Native.BlockImage

public section

namespace SmcTuring.Native.ProgramImage

open Execution BlockImage

@[expose] def owned (mode : Mode) (ctx : Context mode) : Word mode -> Prop :=
  SpacedCombinedImage.Owned mode ctx.whole ctx.origin ctx.gridBase
@[expose] def intact (mode : Mode) (ctx : Context mode) (state : State mode) : Prop :=
  SpacedCombinedImage.Intact mode ctx.whole ctx.origin ctx.gridBase state.memory
@[expose] def represented (mode : Mode) (ctx : Context mode) (source : Dolan.Mov.State) (state : State mode) : Prop :=
  SourceData.Rep mode ctx.gridBase ctx.cells source state.memory
@[expose] def selected (mode : Mode) (ctx : Context mode) (pointer : Nat) (state : State mode) : Prop :=
  exists position : Nat × Bool, position.1 < ctx.cells ∧
    load mode state.memory (Arithmetic.encodeNat mode pointer) = SourceData.heapWord mode ctx.gridBase position
@[expose] def frames (mode : Mode) (frozen : Word mode -> Prop) (initial state : State mode) : Prop :=
  forall word, frozen word -> load mode state.memory word = load mode initial.memory word
@[expose] def view (mode : Mode) (block : Block mode) (state : State mode) : State mode :=
  { state with pc := Arithmetic.encodeNat mode (BlockImage.start mode block) }

/-- A finite static certificate: packet placement and initial metadata setup,
physical separation, and a common data grid. It assumes no future trace,
intermediate Ready, represented result, or simulation theorem. Instantiating
it with the complete emitter is a separate construction obligation. -/
structure Setup (mode : Mode) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode -> Prop) (pointer : Nat) where
  common : forall block, block ∈ schedule -> BlockImage.context mode block = ctx
  initialReady : forall block, block ∈ schedule -> BlockImage.Ready mode block (view mode block initial)
  staticFrozen : forall block, block ∈ schedule -> forall word, Static mode block word -> frozen word
  frozenOwned : forall word, frozen word -> owned mode ctx word
  frozenOutside : forall block, block ∈ schedule -> forall word, frozen word -> Not (MayWrite mode block word)
  capacity : SourceData.Capacity mode ctx.gridBase ctx.cells
  topBefore : ctx.top < ctx.gridBase
  slotBefore : ctx.slot < ctx.gridBase
  pointerOwned : owned mode ctx (Arithmetic.encodeNat mode pointer)
  pointerLayout : forall block, block ∈ schedule -> match block with
    | .immediate _ => Not (MayWrite mode block (Arithmetic.encodeNat mode pointer))
    | .load layout => Arithmetic.encodeNat mode pointer = ReaderImage.label mode layout.address.pointerCallee
    | .store layout => Arithmetic.encodeNat mode pointer = ReaderImage.label mode layout.address.pointerCallee

structure Invariant (mode : Mode) (ctx : Context mode) (initial : State mode)
    (frozen : Word mode -> Prop) (pointer : Nat) (source : Dolan.Mov.State) (state : State mode) : Prop where
  represented : represented mode ctx source state
  intact : intact mode ctx state
  frames : frames mode frozen initial state
  selected : selected mode ctx pointer state

/-- The actual selected heap field supplies every dynamic-pointer premise.
All other setup is transferred from the single original memory snapshot. -/
theorem block_ready (mode : Mode) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode -> Prop) (pointer : Nat)
    (setup : Setup mode ctx schedule initial frozen pointer)
    (block : Block mode) (member : block ∈ schedule) (source : Dolan.Mov.State) (state : State mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = Arithmetic.encodeNat mode (BlockImage.start mode block)) : Ready mode block state := by
  have common := setup.common block member
  apply ready_from_snapshot mode block (view mode block initial) state (setup.initialReady block member) location
  · simpa only [BlockImage.Intact, common, intact] using inv.intact
  · intro word observed
    exact inv.frames word (setup.staticFrozen block member word observed)
  · rcases inv.selected with ⟨position, inside, points⟩
    have targetOwned : owned mode ctx (load mode state.memory (Arithmetic.encodeNat mode pointer)) := by
      rw [points]
      exact SourceData.heap_owned mode ctx.whole ctx.origin ctx.gridBase ctx.cells position setup.capacity inside
    have topFits := SourceData.metadata_fits mode ctx.gridBase ctx.cells ctx.top setup.capacity setup.topBefore
    have slotFits := SourceData.metadata_fits mode ctx.gridBase ctx.cells ctx.slot setup.capacity setup.slotBefore
    have notTop : load mode state.memory (Arithmetic.encodeNat mode pointer) ≠ Arithmetic.encodeNat mode ctx.top := by
      rw [points]
      exact SourceData.heap_not_before mode ctx.gridBase ctx.cells ctx.top position setup.capacity inside topFits setup.topBefore
    have notSlot : load mode state.memory (Arithmetic.encodeNat mode pointer) ≠ Arithmetic.encodeNat mode ctx.slot := by
      rw [points]
      exact SourceData.heap_not_before mode ctx.gridBase ctx.cells ctx.slot position setup.capacity inside slotFits setup.slotBefore
    have positionMatch := setup.pointerLayout block member
    cases block with
    | immediate layout => trivial
    | load layout =>
      change Owned mode (.load layout) (load mode state.memory (ReaderImage.label mode layout.address.pointerCallee))
      rw [←positionMatch]
      simpa only [Owned, common, owned] using targetOwned
    | store layout =>
      change Owned mode (.store layout) (load mode state.memory (ReaderImage.label mode layout.address.pointerCallee)) ∧
        load mode state.memory (ReaderImage.label mode layout.address.pointerCallee) ≠ Arithmetic.encodeNat mode (context mode (.store layout)).top ∧
        load mode state.memory (ReaderImage.label mode layout.address.pointerCallee) ≠ Arithmetic.encodeNat mode (context mode (.store layout)).slot
      rw [←positionMatch, common]
      exact ⟨by simpa only [Owned, common, owned] using targetOwned, notTop, notSlot⟩

theorem block_frames (mode : Mode) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode -> Prop) (pointer : Nat)
    (setup : Setup mode ctx schedule initial frozen pointer)
    (block : Block mode) (member : block ∈ schedule) (source : Dolan.Mov.State) (state : State mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (ready : Ready mode block state) (bounds : Bounds mode block source) :
    frames mode frozen initial (BlockImage.finish mode block source state) := by
  intro word frozenWord
  have common := setup.common block member
  have rep : Rep mode block source state := by simpa only [Rep, common, represented] using inv.represented
  have owner : Owned mode block word := by simpa only [Owned, common, owned] using setup.frozenOwned word frozenWord
  exact (BlockImage.load_frame mode block source state ready bounds rep word owner
    (setup.frozenOutside block member word frozenWord)).trans (inv.frames word frozenWord)

theorem block_selected (mode : Mode) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode -> Prop) (pointer : Nat)
    (setup : Setup mode ctx schedule initial frozen pointer)
    (block : Block mode) (member : block ∈ schedule) (source : Dolan.Mov.State) (state : State mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (ready : Ready mode block state) (bounds : Bounds mode block source) (accepted : accepts block source = true) :
    selected mode ctx pointer (BlockImage.finish mode block source state) := by
  have common := setup.common block member
  have rep : Rep mode block source state := by simpa only [Rep, common, represented] using inv.represented
  have positionMatch := setup.pointerLayout block member
  cases block with
  | immediate layout =>
    rcases inv.selected with ⟨position, inside, points⟩
    have owner : Owned mode (.immediate layout) (Arithmetic.encodeNat mode pointer) := by
      simpa only [Owned, common, owned] using setup.pointerOwned
    exact ⟨position, inside, (BlockImage.load_frame mode (.immediate layout) source state ready bounds rep _ owner positionMatch).trans points⟩
  | load layout =>
    cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
    | none => simp [accepts, instruction, Dolan.Mov.execute, valid] at accepted
    | some position =>
      have inside := LoadImage.pointer_inside mode layout source bounds position valid
      have value := BlockImage.load_pointer mode layout source state ready bounds rep position valid
      rw [←positionMatch] at value
      simpa only [selected, BlockImage.finish, ←common, context] using
        (show exists position : Nat × Bool, position.1 < layout.address.offset.cells ∧
          load mode (LoadImage.finish mode layout source state).memory (Arithmetic.encodeNat mode pointer) =
            SourceData.heapWord mode layout.address.offset.guard.setup.gridBase position from ⟨position, inside, value⟩)
  | store layout =>
    cases valid : Dolan.Mov.address source layout.address.base layout.address.offset.offset with
    | none => simp [accepts, instruction, Dolan.Mov.execute, valid] at accepted
    | some position =>
      have inside := StoreImage.pointer_inside mode layout source bounds position valid
      have value := BlockImage.store_pointer mode layout source state ready bounds rep position valid
      rw [←positionMatch] at value
      simpa only [selected, BlockImage.finish, ←common, context] using
        (show exists position : Nat × Bool, position.1 < layout.address.offset.cells ∧
          load mode (StoreImage.finish mode layout source state).memory (Arithmetic.encodeNat mode pointer) =
            SourceData.heapWord mode layout.address.offset.guard.setup.gridBase position from ⟨position, inside, value⟩)

theorem block_invariant (mode : Mode) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode -> Prop) (pointer : Nat)
    (setup : Setup mode ctx schedule initial frozen pointer)
    (block : Block mode) (member : block ∈ schedule) (source : Dolan.Mov.State) (state : State mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = Arithmetic.encodeNat mode (BlockImage.start mode block))
    (bounds : Bounds mode block source) (accepted : accepts block source = true) :
    Invariant mode ctx initial frozen pointer (result block source) (BlockImage.finish mode block source state) := by
  have ready := block_ready mode ctx schedule initial frozen pointer setup block member source state inv location
  have common := setup.common block member
  have rep : Rep mode block source state := by simpa only [Rep, common, represented] using inv.represented
  have checked := BlockImage.correct mode block source state ready bounds rep
  exact ⟨by simpa only [Rep, common, represented] using checked.represented,
    by simpa only [BlockImage.Intact, common, intact] using checked.intact,
    block_frames mode ctx schedule initial frozen pointer setup block member source state inv ready bounds,
    block_selected mode ctx schedule initial frozen pointer setup block member source state inv ready bounds accepted⟩

structure Outcome (mode : Mode) where
  source : Dolan.Mov.State
  native : State mode
  forms : List (Form mode)
  accepted : Bool

@[expose] def run (mode : Mode) : List (Block mode) -> Dolan.Mov.State -> State mode -> Outcome mode
  | [], source, state => ⟨source, state, [], true⟩
  | block :: rest, source, state =>
      let middle := BlockImage.finish mode block source state
      let updated := result block source
      let leading := program mode block source state
      if accepts block source then
        let later := run mode rest updated middle
        { later with forms := leading ++ later.forms }
      else ⟨updated, middle, leading, false⟩
@[expose] def entry (mode : Mode) (blocks : List (Block mode)) (endPC : Word mode) : Word mode :=
  match blocks with | [] => endPC | block :: _ => Arithmetic.encodeNat mode (BlockImage.start mode block)
@[expose] def Linked (mode : Mode) : List (Block mode) -> Word mode -> Prop
  | [], _ => True
  | block :: rest, endPC => continuation mode block = entry mode rest endPC ∧ Linked mode rest endPC
@[expose] def Bounded (mode : Mode) : List (Block mode) -> Dolan.Mov.State -> Prop
  | [], _ => True
  | block :: rest, source => Bounds mode block source ∧ (accepts block source = true -> Bounded mode rest (result block source))

structure Spec (mode : Mode) (ctx : Context mode) (blocks : List (Block mode))
    (source : Dolan.Mov.State) (state : State mode) (outcome : Outcome mode) : Prop where
  sourceRun : Dolan.Mov.run (blocks.map instruction) source = if outcome.accepted then some outcome.source else none
  represented : represented mode ctx outcome.source outcome.native
  trace : Fetch.Trace mode state outcome.forms outcome.native
  owned : Writes.OwnedRun mode (owned mode ctx) outcome.forms state
  intact : intact mode ctx outcome.native

/-- Composition follows literal source execution and stops at its first trap.
The setup for every actual block is derived from the preserved snapshot and
selected-pointer invariant, rather than supplied by an execution oracle. -/
theorem correct (mode : Mode) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode -> Prop) (pointer : Nat)
    (setup : Setup mode ctx schedule initial frozen pointer)
    (blocks : List (Block mode)) (included : forall block, block ∈ blocks -> block ∈ schedule)
    (source : Dolan.Mov.State) (state : State mode) (endPC : Word mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = entry mode blocks endPC) (linked : Linked mode blocks endPC)
    (bounds : Bounded mode blocks source) : Spec mode ctx blocks source state (run mode blocks source state) := by
  induction blocks generalizing source state with
  | nil => exact ⟨rfl, inv.represented, .nil state, trivial, inv.intact⟩
  | cons block rest ih =>
    have member := included block (by simp)
    have ready := block_ready mode ctx schedule initial frozen pointer setup block member source state inv location
    have common := setup.common block member
    have rep : Rep mode block source state := by simpa only [Rep, common, represented] using inv.represented
    have checked := BlockImage.correct mode block source state ready bounds.1 rep
    have blockOwned : Writes.OwnedRun mode (owned mode ctx) (program mode block source state) state := by
      simpa only [Owned, common, owned] using checked.owned
    have blockRep : represented mode ctx (result block source) (BlockImage.finish mode block source state) := by
      simpa only [Rep, common, represented] using checked.represented
    have blockIntact : intact mode ctx (BlockImage.finish mode block source state) := by
      simpa only [BlockImage.Intact, common, intact] using checked.intact
    cases accepted : accepts block source with
    | false =>
      have sourceStep : Dolan.Mov.execute (instruction block) source = none := by simpa [accepted] using checked.sourceStep
      simpa only [run, accepted, Bool.false_eq_true, ite_false] using
        (show Spec mode ctx (block :: rest) source state
          ⟨result block source, BlockImage.finish mode block source state, program mode block source state, false⟩ from
          ⟨by simp only [List.map_cons, Dolan.Mov.run, sourceStep, Option.bind_none, Bool.false_eq_true, ite_false],
            blockRep, checked.trace, blockOwned, blockIntact⟩)
    | true =>
      have middleInv := block_invariant mode ctx schedule initial frozen pointer setup block member source state inv location bounds.1 accepted
      have nextPC : (BlockImage.finish mode block source state).pc = entry mode rest endPC := by
        simpa only [accepted, Bool.true_eq, ite_true, linked.1] using checked.pc
      have later := ih (fun next nextMember => included next (by simp [nextMember]))
        (result block source) (BlockImage.finish mode block source state) middleInv nextPC linked.2 (bounds.2 accepted)
      have sourceStep : Dolan.Mov.execute (instruction block) source = some (result block source) := by simpa [accepted] using checked.sourceStep
      have prefixRun := (Fetch.trace_run_eq mode checked.trace).symm
      have allOwned : Writes.OwnedRun mode (owned mode ctx)
          (program mode block source state ++ (run mode rest (result block source) (BlockImage.finish mode block source state)).forms) state := by
        rw [Writes.owned_run_append, prefixRun]
        exact ⟨blockOwned, later.owned⟩
      simpa only [run, accepted, Bool.true_eq, ite_true] using
        (show Spec mode ctx (block :: rest) source state
          { run mode rest (result block source) (BlockImage.finish mode block source state) with
            forms := program mode block source state ++ (run mode rest (result block source) (BlockImage.finish mode block source state)).forms } from
          ⟨by simpa only [List.map_cons, Dolan.Mov.run, sourceStep, Option.bind_some] using later.sourceRun,
            later.represented, Fetch.trace_append mode checked.trace later.trace, allOwned, later.intact⟩)


/-- Successful completion reaches the computed backedge and retains the full
reusable invariant. This supplies the next pass's setup after an actual CALL. -/
theorem successful_boundary (mode : Mode) (ctx : Context mode) (schedule : List (Block mode))
    (initial : State mode) (frozen : Word mode -> Prop) (pointer : Nat)
    (setup : Setup mode ctx schedule initial frozen pointer)
    (blocks : List (Block mode)) (included : forall block, block ∈ blocks -> block ∈ schedule)
    (source : Dolan.Mov.State) (state : State mode) (endPC : Word mode)
    (inv : Invariant mode ctx initial frozen pointer source state)
    (location : state.pc = entry mode blocks endPC) (linked : Linked mode blocks endPC)
    (bounds : Bounded mode blocks source) (accepted : (run mode blocks source state).accepted = true) :
    (run mode blocks source state).native.pc = endPC ∧
      Invariant mode ctx initial frozen pointer (run mode blocks source state).source (run mode blocks source state).native := by
  induction blocks generalizing source state with
  | nil => exact ⟨location, inv⟩
  | cons block rest ih =>
    have member := included block (by simp)
    cases acceptedBlock : accepts block source with
    | false => simp only [run, acceptedBlock, Bool.false_eq_true, ite_false] at accepted
    | true =>
      have middleInv := block_invariant mode ctx schedule initial frozen pointer setup block member source state inv location bounds.1 acceptedBlock
      have ready := block_ready mode ctx schedule initial frozen pointer setup block member source state inv location
      have common := setup.common block member
      have rep : Rep mode block source state := by simpa only [Rep, common, represented] using inv.represented
      have checked := BlockImage.correct mode block source state ready bounds.1 rep
      have nextPC : (BlockImage.finish mode block source state).pc = entry mode rest endPC := by
        simpa only [acceptedBlock, Bool.true_eq, ite_true, linked.1] using checked.pc
      have laterAccepted : (run mode rest (result block source) (BlockImage.finish mode block source state)).accepted = true := by
        simpa only [run, acceptedBlock, Bool.true_eq, ite_true] using accepted
      have boundary := ih (fun next nextMember => included next (by simp [nextMember]))
        (result block source) (BlockImage.finish mode block source state) middleInv nextPC linked.2 (bounds.2 acceptedBlock) laterAccepted
      simpa only [run, acceptedBlock, Bool.true_eq, ite_true] using boundary

end SmcTuring.Native.ProgramImage

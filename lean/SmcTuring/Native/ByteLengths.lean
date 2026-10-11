module
public import SmcTuring.Native.RoleInitialization

public section

namespace SmcTuring.Native.ByteLengths

open ControlImage KernelPackets BlockImage

@[expose] def sourceSpan (mode : Mode) : Dolan.Mov.Instruction -> Nat
  | .immediate _ _ => CallsImage.totalSize mode (.relative 0) + ScalarImage.size mode .store
  | .load _ _ _ => 7 * CallsImage.totalSize mode (.relative 0) + 4 * ScalarImage.size mode .store + ScalarImage.size mode .add
  | .store _ _ _ => 8 * CallsImage.totalSize mode (.relative 0) + 3 * ScalarImage.size mode .store + ScalarImage.size mode .add
@[expose] def programSpan (mode : Mode) (source : List Dolan.Mov.Instruction) : Nat := (source.map (sourceSpan mode)).sum
@[expose] def guardSpan (mode : Mode) : Nat := match mode with | .x86 => 206 | .x64 => 244

theorem source_end (mode : Mode) (block : Block mode) :
    KernelPackets.endPosition mode block = BlockImage.start mode block + sourceSpan mode (instruction block) := by
  cases block <;> simp only [KernelPackets.endPosition, BlockImage.start, instruction, sourceSpan,
    ReadScalarImage.endPosition, ReadScalarImage.scalarStart, CallsImage.totalSize,
    LoadImage.readLayout, LoadImage.readStart, StoreImage.storeLayout, StoreImage.readStart,
    AddressImage.pointerStart,
    AddressImage.pointerLayout, AddressImage.guardLayout, AddressImage.baseGuard,
    PointerImage.endPosition, PointerImage.baseLayout, PointerImage.offsetLayout, PointerImage.wordLayout,
    OffsetGuardImage.guardLayout, OffsetGuardImage.readLayout]
  all_goals omega

theorem source_size (mode : Mode) (block : Block mode) :
    ControlPacking.size mode (flatten (segments mode block)) = sourceSpan mode (instruction block) := by
  have extent := ordered_size mode _ _ _ (source_ordered mode block)
  rw [source_end] at extent
  exact Nat.add_left_cancel extent

theorem guard_end (mode : Mode) (layout : GuardImage.Layout mode) :
    GuardPackets.endPosition mode layout = layout.setup.start + guardSpan mode := by
  cases mode <;> simp only [GuardPackets.endPosition, GuardImage.selectionLayout, GuardImage.selectionStart,
    GuardImage.borrowLayout, GuardSelectionImage.callStart, GuardSelectionImage.firstLayout,
    GuardSelectionImage.secondLayout, GuardSelectionImage.thirdLayout, GuardSelectionImage.fourthLayout,
    GuardSelectionImage.updateLayout, ReadScalarImage.endPosition, ReadScalarImage.scalarStart,
    BorrowMaskImage.storeStart, GuardSetupImage.endPosition, GuardSetupImage.boundaryStart,
    GuardSetupImage.scratchStart, GuardSetupImage.candidateStart, GuardSetupImage.resumeStart,
    ReaderImage.totalSize, ScalarImage.size, CallsImage.totalSize, CallsImage.resetSize,
    instructionLength, MemoryOp.prefix, MemoryOp.trailer, wordPrefix, ScalarImage.memoryOp, Mode.wordBytes,
    List.length_cons, List.length_nil, reduceCtorEq, ite_false, guardSpan]

theorem guard_size (mode : Mode) (layout : GuardImage.Layout mode) :
    ControlPacking.size mode (GuardPackets.packets mode layout) = guardSpan mode := by
  have extent := ordered_size mode _ _ _ (GuardPackets.ordered mode layout)
  rw [guard_end] at extent
  exact Nat.add_left_cancel extent

theorem program_size (mode : Mode) (blocks : List (Block mode)) :
    ControlPacking.size mode (flatten (programSegments mode blocks)) = programSpan mode (blocks.map instruction) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    change ControlPacking.size mode (flatten (segments mode block ++ programSegments mode rest)) = _
    rw [show flatten (segments mode block ++ programSegments mode rest) =
      flatten (segments mode block) ++ flatten (programSegments mode rest) from List.flatMap_append,
      Fragment.size_append, source_size, ih]
    rfl

/-- A single capacity bound on the complete source body establishes every
computed block bound and the exact physical backedge; no future state is used. -/
theorem compile_extent (mode : Mode) (roles : KernelImage.Roles mode) (start : Nat)
    (source : List Dolan.Mov.Instruction) (blocks : List (Block mode)) (endPC : Word mode)
    (compiled : KernelImage.compile mode roles start source = some (blocks, endPC))
    (fits : start + programSpan mode source < 2 ^ (8 * mode.wordBytes)) :
    endPC.toNat = start + programSpan mode source ∧
      (forall block, block ∈ blocks -> KernelPackets.endPosition mode block < 2 ^ (8 * mode.wordBytes)) := by
  induction source generalizing start blocks endPC with
  | nil =>
    simp only [KernelImage.compile, Option.some.injEq, Prod.mk.injEq] at compiled
    rcases compiled with ⟨rfl, rfl⟩
    exact ⟨Arithmetic.encode_nat_toNat mode start fits, by simp⟩
  | cons source rest ih =>
    cases first : KernelImage.lower mode roles start source with
    | none => simp only [KernelImage.compile, first, Option.bind_none, reduceCtorEq] at compiled
    | some block =>
      cases tail : KernelImage.compile mode roles (continuation mode block).toNat rest with
      | none => simp only [KernelImage.compile, first, Option.bind_some, tail, Option.map_none, reduceCtorEq] at compiled
      | some result =>
        rcases result with ⟨trailing, trailingEnd⟩
        simp only [KernelImage.compile, first, Option.bind_some, tail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        have properties := KernelImage.lower_properties mode roles start source block first
        have endPosition : KernelPackets.endPosition mode block = start + sourceSpan mode source := by
          rw [source_end, properties.1, properties.2.1]
        have full : start + sourceSpan mode source + programSpan mode rest < 2 ^ (8 * mode.wordBytes) := by
          simpa only [programSpan, List.map_cons, List.sum_cons, Nat.add_assoc] using fits
        have blockFits : KernelPackets.endPosition mode block < 2 ^ (8 * mode.wordBytes) := by rw [endPosition]; omega
        have next : (continuation mode block).toNat = start + sourceSpan mode source := by
          rw [←source_continuation, Arithmetic.encode_nat_toNat mode _ blockFits, endPosition]
        have later := ih _ trailing trailingEnd tail (by simpa only [next] using full)
        constructor
        · simpa only [programSpan, List.map_cons, List.sum_cons, next, Nat.add_assoc] using later.1
        · intro observed member
          rcases List.mem_cons.mp member with same | laterMember
          · subst observed; exact blockFits
          · exact later.2 observed laterMember

theorem kernel_span (mode : Mode) : programSpan mode Dolan.Mov.kernelProgram =
    (match mode with | .x86 => 9382 | .x64 => 10816) := by
  cases mode <;> decide

end SmcTuring.Native.ByteLengths

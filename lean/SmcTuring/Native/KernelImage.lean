module
public import SmcTuring.Native.LoopImage
public import SmcTuring.Dolan.Kernel

public section

namespace SmcTuring.Native.KernelImage

open BlockImage

/-- Static role addresses shared by the generator's 64 source blocks. The
complete padded image is carried by the guard's placement context. -/
structure Roles (mode : Mode) where
  guard : GuardImage.Layout mode
  cells : Nat
  baseGuardStart : Nat
  pointerCallee : Nat
  wordCallee : Nat
  registerCallee : Dolan.Mov.Register -> Nat
  constantCallee : Bool -> Nat
  constant : Bool -> Nat

@[expose] def context (mode : Mode) (roles : Roles mode) : Context mode :=
  ⟨roles.guard.setup.whole, roles.guard.setup.origin, roles.guard.setup.gridBase,
    roles.cells, roles.guard.setup.top, roles.guard.setup.slot⟩
@[expose] def reader (mode : Mode) (roles : Roles mode) (start callee : Nat) (initial : Word mode) : ReadInvocationImage.Layout mode :=
  ⟨start, callee, roles.guard.setup.top, roles.guard.setup.slot, roles.guard.setup.origin,
    roles.guard.setup.gridBase, initial, roles.guard.setup.whole⟩
@[expose] def address (mode : Mode) (roles : Roles mode) (start : Nat) (base offset : Dolan.Mov.Register) : AddressImage.Layout mode :=
  ⟨⟨start, roles.registerCallee offset, SourceData.registerWord mode roles.guard.setup.gridBase offset,
      { roles.guard with sense := .offset }, offset, roles.cells⟩,
    roles.registerCallee base, roles.wordCallee, roles.pointerCallee, roles.baseGuardStart,
    SourceData.registerWord mode roles.guard.setup.gridBase base,
    Arithmetic.encodeNat mode (roles.pointerCallee + ReaderImage.labelOffset mode), base⟩
@[expose] def supports : Dolan.Mov.Instruction -> Bool
  | .immediate _ (.address _) => false
  | _ => true
@[expose] def lower (mode : Mode) (roles : Roles mode) (start : Nat) : Dolan.Mov.Instruction -> Option (Block mode)
  | .immediate destination (.offset choice) => some (.immediate
      ⟨⟨reader mode roles start (roles.constantCallee choice) (Arithmetic.encodeNat mode (roles.constant choice)),
        SourceData.registerAddress mode roles.guard.setup.gridBase destination⟩,
        destination, roles.constant choice, choice, roles.cells⟩)
  | .immediate _ (.address _) => none
  | .load destination base offset => some (.load
      ⟨address mode roles start base offset, destination,
        SourceValues.encodeWord mode roles.guard.setup.gridBase (.address 0)⟩)
  | .store base offset source => some (.store
      ⟨address mode roles start base offset, source, roles.registerCallee source,
        SourceData.registerWord mode roles.guard.setup.gridBase source,
        SourceValues.encodeWord mode roles.guard.setup.gridBase (.address 0)⟩)

/-- Literal instruction operands and source block PCs survive lowering. -/
theorem lower_properties (mode : Mode) (roles : Roles mode) (start : Nat) (source : Dolan.Mov.Instruction)
    (block : Block mode) (lowered : lower mode roles start source = some block) :
    instruction block = source ∧ BlockImage.start mode block = start ∧ BlockImage.context mode block = context mode roles := by
  cases source with
  | immediate destination value =>
    cases value with
    | address cell => simp [lower] at lowered
    | offset choice =>
      simp only [lower, Option.some.injEq] at lowered
      subst block
      exact ⟨rfl, rfl, rfl⟩
  | load destination base offset =>
    simp only [lower, Option.some.injEq] at lowered
    subst block
    exact ⟨rfl, rfl, rfl⟩
  | store base offset source =>
    simp only [lower, Option.some.injEq] at lowered
    subst block
    exact ⟨rfl, rfl, rfl⟩

@[expose] def compile (mode : Mode) (roles : Roles mode) : Nat -> List Dolan.Mov.Instruction -> Option (List (Block mode) × Word mode)
  | start, [] => some ([], Arithmetic.encodeNat mode start)
  | start, source :: rest => (lower mode roles start source).bind fun block =>
      (compile mode roles (continuation mode block).toNat rest).map fun trailing => (block :: trailing.1, trailing.2)

/-- The layout pass is contiguous in encoded PCs and names exactly the source
instruction list. No future execution or source data influences the layout. -/
theorem compile_properties (mode : Mode) (roles : Roles mode) (start : Nat) (source : List Dolan.Mov.Instruction)
    (blocks : List (Block mode)) (endPC : Word mode) (compiled : compile mode roles start source = some (blocks, endPC)) :
    blocks.map instruction = source ∧
      ProgramImage.entry mode blocks endPC = Arithmetic.encodeNat mode start ∧
      ProgramImage.Linked mode blocks endPC ∧
      (forall block, block ∈ blocks -> BlockImage.context mode block = context mode roles) := by
  induction source generalizing start blocks endPC with
  | nil =>
    simp only [compile, Option.some.injEq, Prod.mk.injEq] at compiled
    rcases compiled with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, trivial, by simp⟩
  | cons source rest ih =>
    cases first : lower mode roles start source with
    | none => simp only [compile, first, Option.bind_none, reduceCtorEq] at compiled
    | some block =>
      cases trailing : compile mode roles (continuation mode block).toNat rest with
      | none => simp only [compile, first, Option.bind_some, trailing, Option.map_none, reduceCtorEq] at compiled
      | some result =>
        rcases result with ⟨tail, tailEnd⟩
        simp only [compile, first, Option.bind_some, trailing, Option.map_some, Option.some.injEq, Prod.mk.injEq] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        have firstProperties := lower_properties mode roles start source block first
        have tailProperties := ih (continuation mode block).toNat tail tailEnd trailing
        have boundary : continuation mode block = ProgramImage.entry mode tail tailEnd := by
          rw [tailProperties.2.1, Arithmetic.encodeNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact ⟨by simp only [List.map_cons, firstProperties.1, tailProperties.1],
          by simp only [ProgramImage.entry, firstProperties.2.1],
          ⟨boundary, tailProperties.2.2.1⟩,
          by
            intro observed member
            rcases List.mem_cons.mp member with same | later
            · subst observed; exact firstProperties.2.2
            · exact tailProperties.2.2.2 observed later⟩

theorem compile_total (mode : Mode) (roles : Roles mode) (start : Nat) (source : List Dolan.Mov.Instruction)
    (supported : source.all supports = true) : exists blocks endPC, compile mode roles start source = some (blocks, endPC) := by
  induction source generalizing start with
  | nil => exact ⟨[], Arithmetic.encodeNat mode start, rfl⟩
  | cons source rest ih =>
    have both : supports source = true ∧ rest.all supports = true := by simpa only [List.all_cons, Bool.and_eq_true] using supported
    have lowered : exists block, lower mode roles start source = some block := by
      cases source with
      | immediate destination value =>
        cases value with
        | address cell => exact False.elim (by simpa only [supports, Bool.false_eq_true] using both.1)
        | offset choice => exact ⟨_, rfl⟩
      | load destination base offset => exact ⟨_, rfl⟩
      | store base offset source => exact ⟨_, rfl⟩
    rcases lowered with ⟨block, lowered⟩
    rcases ih (continuation mode block).toNat both.2 with ⟨tail, endPC, compiled⟩
    exact ⟨block :: tail, endPC, by simp only [compile, lowered, Option.bind_some, compiled, Option.map_some]⟩

theorem kernel_supported : Dolan.Mov.kernelProgram.all supports = true := by decide

/-- The actual exported Dolan kernel always lowers to exactly 64 native source
blocks, with a computed contiguous backedge and unchanged instruction operands. -/
theorem fixed_kernel (mode : Mode) (roles : Roles mode) (start : Nat) :
    exists blocks endPC, compile mode roles start Dolan.Mov.kernelProgram = some (blocks, endPC) ∧
      blocks.map instruction = Dolan.Mov.kernelProgram ∧ blocks.length = 64 ∧
      ProgramImage.entry mode blocks endPC = Arithmetic.encodeNat mode start ∧
      ProgramImage.Linked mode blocks endPC ∧
      (forall block, block ∈ blocks -> BlockImage.context mode block = context mode roles) := by
  rcases compile_total mode roles start Dolan.Mov.kernelProgram kernel_supported with ⟨blocks, endPC, compiled⟩
  have properties := compile_properties mode roles start Dolan.Mov.kernelProgram blocks endPC compiled
  have length : blocks.length = 64 := by
    have sizes := congrArg List.length properties.1
    simpa only [List.length_map, Dolan.Mov.kernel_length] using sizes
  exact ⟨blocks, endPC, compiled, properties.1, length, properties.2⟩

end SmcTuring.Native.KernelImage

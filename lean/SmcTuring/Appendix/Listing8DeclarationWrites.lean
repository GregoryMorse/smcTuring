module
public import SmcTuring.Appendix.Listing8OriginalOwnerWrites
public import SmcTuring.Appendix.Listing8NodeTrace
public import SmcTuring.Appendix.Listing8TableTrace

public section
namespace SmcTuring.Appendix.Listing8DeclarationWrites
open Native Listing8Prototypes

theorem node_fields (mode : Mode) (codeStart codeEnd pc : Nat) (v : Listing8NodeBlock.Values mode)
    (inside : codeStart≤pc ∧ pc+nodeSpan mode≤codeEnd)
    (back : StringWrites.WordOwned mode codeStart codeEnd v.back)
    (forward : StringWrites.WordOwned mode codeStart codeEnd v.forward) :
    ∀ owner∈Listing8NodeBlock.owners mode pc v,Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner := by
  intro owner member
  simp only [Listing8NodeBlock.owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · change codeStart≤pc+6 ∧ pc+10≤codeEnd
    dsimp [nodeSpan] at inside;omega
  · refine ⟨?_,back⟩
    dsimp [backEntry,nodeSpan] at inside ⊢;omega
  · refine ⟨?_,forward⟩
    dsimp [forwardEntry,backEntry,nodeSpan] at inside ⊢;omega

theorem node_owned (mode : Mode) (codeStart codeEnd pc : Nat) (v : Listing8NodeBlock.Values mode)
    (bounds : Listing8NodeBlock.Bounds mode pc v)
    (placed : ∀ owner∈Listing8NodeBlock.owners mode pc v,Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (current : ByteMemory.bytesAt state.principal.memory pc (nodeSpan mode)=Listing8NodeBlock.bytes mode pc v) :
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8NodeBlock.program mode pc v).map (StringStoreWrites.liftDword mode)) state :=
  Listing8OriginalOwnerWrites.owned mode codeStart codeEnd (Listing8NodeBlock.owners mode pc v) pc
    (Listing8NodeBlock.contiguous mode pc v) (Listing8NodeBlock.valid mode pc v bounds) placed state entry
    (Listing8NodeBlock.current mode pc v state.principal.memory current)

theorem transition_fields (mode : Mode) (codeStart codeEnd pc : Nat) (v : Listing8CopyImage.Values mode)
    (inside : codeStart≤pc ∧ pc+transitionSpan mode≤codeEnd)
    (next : StringWrites.WordOwned mode codeStart codeEnd v.next)
    (state : StringWrites.WordOwned mode codeStart codeEnd v.newState) :
    ∀ owner∈Listing8TransitionBlock.owners mode pc v,Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner := by
  intro owner member
  simp only [Listing8TransitionBlock.owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨?_,next⟩
    dsimp [transitionSpan] at inside;omega
  · change codeStart≤currentEntry mode pc+6 ∧ currentEntry mode pc+10≤codeEnd
    dsimp [currentEntry,transitionSpan] at inside ⊢;omega
  · change codeStart≤newEntry mode pc+6 ∧ newEntry mode pc+10≤codeEnd
    dsimp [newEntry,currentEntry,transitionSpan] at inside ⊢;omega
  · change codeStart≤directionEntry mode pc+6 ∧ directionEntry mode pc+10≤codeEnd
    dsimp [directionEntry,newEntry,currentEntry,transitionSpan] at inside ⊢;omega
  · refine ⟨?_,state⟩
    dsimp [stateEntry,directionEntry,newEntry,currentEntry,transitionSpan] at inside ⊢;omega

theorem transition_owned (mode : Mode) (codeStart codeEnd pc : Nat) (v : Listing8CopyImage.Values mode)
    (bounds : Listing8TransitionBlock.Bounds mode pc v)
    (placed : ∀ owner∈Listing8TransitionBlock.owners mode pc v,Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (current : ByteMemory.bytesAt state.principal.memory pc (transitionSpan mode)=
      transitionBytes mode pc v.next v.newState v.rule v.fresh v.direction) :
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8TransitionBlock.program mode pc v).map (StringStoreWrites.liftDword mode)) state :=
  Listing8OriginalOwnerWrites.owned mode codeStart codeEnd (Listing8TransitionBlock.owners mode pc v) pc
    (Listing8TransitionBlock.contiguous mode pc v) (Listing8TransitionBlock.valid mode pc v bounds) placed state entry
    (Listing8TransitionBlock.current mode pc v state.principal.memory current)

@[expose] def NodePlaced (mode : Mode) (codeStart codeEnd : Nat) : Nat → List (Listing8NodeBlock.Values mode) → Prop
  | _,[] => True
  | pc,v::rest => (∀ owner∈Listing8NodeBlock.owners mode pc v,Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner) ∧
      NodePlaced mode codeStart codeEnd (pc+nodeSpan mode) rest
@[expose] def TransitionPlaced (mode : Mode) (codeStart codeEnd : Nat) : Nat → List (Listing8CopyImage.Values mode) → Prop
  | _,[] => True
  | pc,v::rest => (∀ owner∈Listing8TransitionBlock.owners mode pc v,Listing8OriginalOwnerWrites.Placement mode codeStart codeEnd owner) ∧
      TransitionPlaced mode codeStart codeEnd (pc+transitionSpan mode) rest

theorem nodes_owned (mode : Mode) (codeStart codeEnd pc : Nat) (table : List (Listing8NodeBlock.Values mode))
    (valid : Listing8NodeTable.Valid mode pc table) (placed : NodePlaced mode codeStart codeEnd pc table)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (current : Listing8NodeTable.Initial mode pc table state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8NodeTrace.program mode pc table).map (StringStoreWrites.liftDword mode)) state := by
  induction table generalizing pc state with
  | nil => trivial
  | cons v table ih =>
    have packet:=Listing8NodeTable.head_current mode pc v table state.principal.memory current
    have actual:=Listing8NodeBlock.result mode pc v valid.1 state entry packet
    have tailImage : Listing8NodeTable.Initial mode (pc+nodeSpan mode) table (Listing8NodeBlock.finish mode pc v state).principal.memory := by
      rw [actual.2.1];exact Listing8NodeTable.tail_current mode pc v table state.principal.memory current
    have tail:=ih (pc+nodeSpan mode) valid.2 placed.2 (Listing8NodeBlock.finish mode pc v state) actual.1 tailImage
    rw [Listing8NodeTrace.program,List.map_append,StringWrites.owned_run_append,
      StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode (Listing8NodeBlock.trace mode pc v valid.1 state entry packet))]
    exact ⟨node_owned mode codeStart codeEnd pc v valid.1 placed.1 state entry packet,tail⟩

theorem transitions_owned (mode : Mode) (codeStart codeEnd pc : Nat) (table : List (Listing8CopyImage.Values mode))
    (valid : Listing8TransitionTable.Valid mode pc table) (placed : TransitionPlaced mode codeStart codeEnd pc table)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (current : Listing8TransitionTable.Initial mode pc table state.principal.memory) :
    StringWrites.OwnedRun mode codeStart codeEnd ((Listing8TableTrace.program mode pc table).map (StringStoreWrites.liftDword mode)) state := by
  induction table generalizing pc state with
  | nil => trivial
  | cons v table ih =>
    have packet:=Listing8TransitionTable.head_current mode pc v table state.principal.memory current
    have actual:=Listing8TransitionBlock.result mode pc v valid.1 state entry packet
    have tailImage : Listing8TransitionTable.Initial mode (pc+transitionSpan mode) table (Listing8TransitionBlock.finish mode pc v state).principal.memory := by
      rw [actual.2.1];exact Listing8TransitionTable.tail_current mode pc v table state.principal.memory current
    have tail:=ih (pc+transitionSpan mode) valid.2 placed.2 (Listing8TransitionBlock.finish mode pc v state) actual.1 tailImage
    rw [Listing8TableTrace.program,List.map_append,StringWrites.owned_run_append,
      StringWrites.trace_run_eq mode (StringDwordWritesBridge.trace mode (Listing8TransitionBlock.trace mode pc v valid.1 state entry packet))]
    exact ⟨transition_owned mode codeStart codeEnd pc v valid.1 placed.1 state entry packet,tail⟩

end SmcTuring.Appendix.Listing8DeclarationWrites

module
public import SmcTuring.Appendix.Listing8OwnerImage

public section
namespace SmcTuring.Appendix.Listing8CopiedOwners
open Native Listing8Prototypes Listing8CopyImage Listing8OwnerImage

/-- Initial graph/field capacities, placement and signed reaches only.
No future byte image, readiness or execution assertion is a field. -/
structure Bounds (mode : Mode) (l : Layout) (v : Values mode) : Prop where
  graph : ∀ value ∈ [v.back,v.forward,v.next,v.newState],
    (value.toNat+mode.wordBytes ≤ l.start ∨ codeEnd mode l ≤ value.toNat) ∧
    value.toNat+mode.wordBytes < 2^(8*mode.wordBytes)
  directionAfter : Listing8LiteralInput.endPC mode l.input ≤ l.direction
  directionFits : l.direction+10 < 2^(8*mode.wordBytes)
  nodeDirection : l.sourceNode+nodeSpan mode ≤ l.direction+6 ∨ l.direction+10 ≤ l.sourceNode
  transitionDirection : l.sourceTransition+transitionSpan mode ≤ l.direction+6 ∨ l.direction+10 ≤ l.sourceTransition
  tapeReach : mode = .x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input)
  ruleReach : mode = .x64 → Relocation.SignedDelta (currentEntry mode (transitionParams mode l).destination+10) (Listing8LiteralInput.scalarField mode l.input)
  freshReach : mode = .x64 → Relocation.SignedDelta (newEntry mode (transitionParams mode l).destination+10) (Listing8LiteralInput.updateStart mode l.input+6)
  directionReach : mode = .x64 → Relocation.SignedDelta (directionEntry mode (transitionParams mode l).destination+10) (l.direction+6)

@[expose] def program (mode : Mode) (l : Layout) (v : Values mode) :=
  Listing8Initializer.program mode l v ++ Listing8OwnerSequence.program mode (owners mode l v)
@[expose] def finish (mode : Mode) (l : Layout) (v : Values mode) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8OwnerSequence.finish mode (owners mode l v) (state mode l v backing seed)

theorem chain (mode : Mode) (l : Layout) (v : Values mode) :
    Listing8OwnerSequence.Contiguous mode (backEntry mode (nodeParams mode l).destination) (owners mode l v) := by
  cases mode <;> simp [owners,Listing8OwnerSequence.Contiguous,Listing8OwnerSequence.pc,Listing8OwnerSequence.span,
    nodeParams,transitionParams,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,patchLayout,
    backEntry,forwardEntry,stateEntry,directionEntry,newEntry,currentEntry,nodeSpan,pointerSpan,ReaderImage.totalSize,Nat.add_assoc]

theorem endpoint (mode : Mode) (l : Layout) (v : Values mode) :
    backEntry mode (nodeParams mode l).destination+Listing8OwnerSequence.total mode (owners mode l v) = codeEnd mode l := by
  cases mode <;> simp [owners,Listing8OwnerSequence.total,Listing8OwnerSequence.span,
    nodeParams,transitionParams,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,Listing8ModeOffsets.endPC,patchLayout,codeEnd,
    backEntry,nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,Nat.add_assoc]

theorem source_limits (mode : Mode) (l : Layout) (r : Resources mode l) :
    l.sourceNode+nodeSpan mode < 2^(8*mode.wordBytes) ∧ l.sourceTransition+transitionSpan mode < 2^(8*mode.wordBytes) := by
  have a := r.node.sourceFits
  have b := r.transition.sourceFits
  change l.sourceNode+max (nodeSpan mode) mode.wordBytes < _ at a
  change l.sourceTransition+max (transitionSpan mode) mode.wordBytes < _ at b
  have m := Nat.le_max_left (nodeSpan mode) mode.wordBytes
  have n := Nat.le_max_left (transitionSpan mode) mode.wordBytes
  constructor <;> omega

theorem pointer_valid (mode : Mode) (l : Layout) (r : Resources mode l)
    (sourceBase size source pc : Nat) (value : Word mode)
    (sourceFits : sourceBase+size < 2^(8*mode.wordBytes))
    (sourceWithin : sourceBase ≤ source ∧ source+pointerSpan mode ≤ sourceBase+size)
    (sourceOutside : sourceBase+size ≤ l.start ∨ Listing8LiteralInput.endPC mode l.input ≤ sourceBase)
    (pcMember : pc ∈ pointerPositions mode l)
    (graph : (value.toNat+mode.wordBytes ≤ l.start ∨ codeEnd mode l ≤ value.toNat) ∧ value.toNat+mode.wordBytes < 2^(8*mode.wordBytes)) :
    Listing8OwnerSequence.Valid mode (.pointer source pc value) := by
  have codeFits := block_capacity mode l r
  have p := pointer_bounds mode l pc pcMember
  have e := code_to_input mode l r
  refine ⟨by omega,by omega,?_,?_,graph.2⟩
  · rcases sourceOutside with early | late <;> omega
  · rcases graph.1 with early | late <;> omega

theorem scalar_bounds (mode : Mode) (l : Layout) :
    l.input.start ≤ Listing8LiteralInput.scalarField mode l.input ∧
    Listing8LiteralInput.scalarField mode l.input+4 ≤ Listing8LiteralInput.endPC mode l.input ∧
    l.input.start ≤ Listing8LiteralInput.updateStart mode l.input+6 ∧
    Listing8LiteralInput.updateStart mode l.input+10 ≤ Listing8LiteralInput.endPC mode l.input := by
  have scalar := (Listing8LiteralInput.positions mode l.input).2.1
  have update := (Listing8LiteralInput.positions mode l.input).2.2.2.2.1
  have ending := (Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at scalar update ending <;> omega

theorem scalar_code_bounds (mode : Mode) (l : Layout) :
    currentEntry mode (transitionParams mode l).destination+10 ≤ codeEnd mode l ∧
    newEntry mode (transitionParams mode l).destination+10 ≤ codeEnd mode l ∧
    directionEntry mode (transitionParams mode l).destination+10 ≤ codeEnd mode l := by
  cases mode <;> simp [transitionParams,codeEnd,patchLayout,Listing8ModeOffsets.endPC,Listing8ModeOffsets.transitionEntry,
    currentEntry,newEntry,directionEntry,nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize]

theorem valid (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (b : Bounds mode l v) :
    ∀ owner ∈ owners mode l v, Listing8OwnerSequence.Valid mode owner := by
  have limits := source_limits mode l r
  have nodeBack : l.sourceNode ≤ backEntry mode l.sourceNode ∧ backEntry mode l.sourceNode+pointerSpan mode ≤ l.sourceNode+nodeSpan mode := by
    simp [backEntry,nodeSpan]
    omega
  have nodeForward : l.sourceNode ≤ forwardEntry mode l.sourceNode ∧ forwardEntry mode l.sourceNode+pointerSpan mode ≤ l.sourceNode+nodeSpan mode := by
    simp [forwardEntry,backEntry,nodeSpan];omega
  have transitionState : l.sourceTransition ≤ stateEntry mode l.sourceTransition ∧ stateEntry mode l.sourceTransition+pointerSpan mode ≤ l.sourceTransition+transitionSpan mode := by
    simp [stateEntry,directionEntry,newEntry,currentEntry,transitionSpan];omega
  have fields := scalar_bounds mode l
  have inputFits := r.inputFits
  have codeFits := block_capacity mode l r
  have codes := scalar_code_bounds mode l
  intro owner member
  simp only [owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointer_valid mode l r l.sourceNode (nodeSpan mode) _ _ _ limits.1 nodeBack r.nodeOutside
      (by simp [pointerPositions]) (b.graph _ (by simp))
  · exact pointer_valid mode l r l.sourceNode (nodeSpan mode) _ _ _ limits.1 nodeForward r.nodeOutside
      (by simp [pointerPositions]) (b.graph _ (by simp))
  · exact pointer_valid mode l r l.sourceTransition (transitionSpan mode) _ _ _ limits.2
      ⟨Nat.le_refl _,by unfold transitionSpan;omega⟩ r.transitionOutside (by simp [pointerPositions]) (b.graph _ (by simp))
  · exact ⟨by omega,by omega,b.ruleReach⟩
  · exact ⟨by omega,by omega,b.freshReach⟩
  · exact ⟨by omega,by have fits := b.directionFits;omega,b.directionReach⟩
  · exact pointer_valid mode l r l.sourceTransition (transitionSpan mode) _ _ _ limits.2 transitionState r.transitionOutside
      (by simp [pointerPositions]) (b.graph _ (by simp))

/-- Every initial instruction/source window is in one of the three actual
initialized regions. This establishes scalar-store frames from placement. -/
theorem window_bounds (mode : Mode) (l : Layout) (v : Values mode) (owner : Owner mode) (member : owner ∈ owners mode l v)
    (window : Nat × Nat) (windowMember : window ∈ Listing8OwnerSequence.windows mode owner) :
    (l.start ≤ window.1 ∧ window.1+window.2 ≤ codeEnd mode l) ∨
    (l.sourceNode ≤ window.1 ∧ window.1+window.2 ≤ l.sourceNode+nodeSpan mode) ∨
    (l.sourceTransition ≤ window.1 ∧ window.1+window.2 ≤ l.sourceTransition+transitionSpan mode) := by
  have before := endpoint_lower mode l.start (nodeSpan mode)
  have next := endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change l.start ≤ secondStart mode l at before
  change secondStart mode l ≤ patchStart mode l at next
  simp only [owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Listing8OwnerSequence.windows,List.mem_cons,List.not_mem_nil,or_false] at windowMember <;>
      rcases windowMember with rfl | rfl <;>
        cases mode <;> simp [pointer_length,backEntry,forwardEntry,stateEntry,directionEntry,newEntry,currentEntry,
          nodeParams,transitionParams,codeEnd,patchLayout,Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,Listing8ModeOffsets.endPC,
          nodeSpan,transitionSpan,pointerSpan,ReaderImage.totalSize,Nat.add_assoc] <;> omega

theorem outside (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (b : Bounds mode l v) :
    ∀ writer ∈ owners mode l v, ∀ reader ∈ owners mode l v, Listing8OwnerSequence.Outside mode writer reader := by
  have fields := scalar_bounds mode l
  have codeToInput := r.inputAfter
  have inputToDirection := b.directionAfter
  have target_frame (target : Nat)
      (codeBefore : codeEnd mode l ≤ target)
      (nodeOutside : l.sourceNode+nodeSpan mode ≤ target ∨ target+4 ≤ l.sourceNode)
      (transitionOutside : l.sourceTransition+transitionSpan mode ≤ target ∨ target+4 ≤ l.sourceTransition)
      (reader : Owner mode) (rm : reader ∈ owners mode l v) (window : Nat × Nat) (wm : window ∈ Listing8OwnerSequence.windows mode reader) :
      target+4 ≤ window.1 ∨ window.1+window.2 ≤ target := by
    rcases window_bounds mode l v reader rm window wm with code | node | transition
    · right;omega
    · rcases nodeOutside with early | late <;> omega
    · rcases transitionOutside with early | late <;> omega
  have input_frame (target : Nat) (within : l.input.start ≤ target ∧ target+4 ≤ Listing8LiteralInput.endPC mode l.input) :
      codeEnd mode l ≤ target ∧ (l.sourceNode+nodeSpan mode ≤ target ∨ target+4 ≤ l.sourceNode) ∧
      (l.sourceTransition+transitionSpan mode ≤ target ∨ target+4 ≤ l.sourceTransition) := by
    have lower : l.start ≤ l.input.start := by have d := destinations mode l;omega
    refine ⟨by omega,?_,?_⟩
    · rcases r.nodeOutside with early | late <;> omega
    · rcases r.transitionOutside with early | late <;> omega
  intro writer wm reader rm
  simp only [owners,List.mem_cons,List.not_mem_nil,or_false] at wm
  rcases wm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · have f := input_frame _ ⟨fields.1,fields.2.1⟩
    exact target_frame _ f.1 f.2.1 f.2.2 reader rm
  · have f := input_frame _ ⟨fields.2.2.1,fields.2.2.2⟩
    exact target_frame _ f.1 f.2.1 f.2.2 reader rm
  · exact target_frame _ (by have e := code_to_input mode l r;omega) b.nodeDirection b.transitionDirection reader rm
  · trivial

/-- The actual Listing 8 execution now continues through every copied
pointer and scalar owner, in its printed order and the same current-byte
state/decoder as both TRANSFERDATA calls and all retargets. -/
theorem trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (b : Bounds mode l v)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringDword.Trace mode (initial mode l v backing seed) (program mode l v) (finish mode l v backing seed) :=
  StringDword.trace_append mode (Listing8Initializer.trace mode l v r backing seed)
    (Listing8OwnerSequence.trace mode (owners mode l v) _ (chain mode l v) (valid mode l v r b) (outside mode l v r b) _
      (entry mode l v r b.tapeReach backing seed) (initial_current mode l v r b.tapeReach backing seed))

theorem instruction_count (mode : Mode) (l : Layout) (v : Values mode) :
    (program mode l v).length = if mode = .x86 then 69 else 71 := by
  rw [program,List.length_append,Listing8Initializer.instruction_count]
  cases mode <;> simp [Listing8OwnerSequence.program,owners,Listing8OwnerSequence.forms,Listing8CopiedPointer.forms]

theorem result (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (b : Bounds mode l v)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode l v backing seed).principal.pc = Arithmetic.encodeNat mode (codeEnd mode l) ∧
    (finish mode l v backing seed).principal.memory =
      DwordCode.put (DwordCode.put (DwordCode.put (state mode l v backing seed).principal.memory
        (Listing8LiteralInput.scalarField mode l.input) v.rule) (Listing8LiteralInput.updateStart mode l.input+6) v.fresh) (l.direction+6) v.direction ∧
    (finish mode l v backing seed).principal.stack = (state mode l v backing seed).principal.stack ∧
    (finish mode l v backing seed).principal.carry = (state mode l v backing seed).principal.carry ∧
    (finish mode l v backing seed).sourceIndex = (state mode l v backing seed).sourceIndex ∧
    (finish mode l v backing seed).destinationIndex = (state mode l v backing seed).destinationIndex ∧
    (finish mode l v backing seed).backwards = (state mode l v backing seed).backwards := by
  have result := Listing8OwnerSequence.result mode (owners mode l v) _ (chain mode l v) (valid mode l v r b) (outside mode l v r b) _
    (entry mode l v r b.tapeReach backing seed) (initial_current mode l v r b.tapeReach backing seed)
  rw [endpoint] at result
  simpa only [finish,owners,Listing8OwnerSequence.writes,Listing8OwnerSequence.write] using result

theorem retained_image (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l) (b : Bounds mode l v)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8OwnerSequence.Intact mode (owners mode l v) (finish mode l v backing seed).principal.memory :=
  Listing8OwnerSequence.retained_image mode (owners mode l v) _ (chain mode l v) (valid mode l v r b) (outside mode l v r b) _
    (entry mode l v r b.tapeReach backing seed) (initial_current mode l v r b.tapeReach backing seed)

end SmcTuring.Appendix.Listing8CopiedOwners

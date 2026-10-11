module
public import SmcTuring.Appendix.Listing8RetargetOwnerFields
public import SmcTuring.Appendix.Listing8CrossMacroCatalog

public section
namespace SmcTuring.Appendix.Listing8MacroOwnerFrames
open Native Listing8CopyImage Listing8SourceGraph Listing8Prototypes
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
abbrev Targets:=Listing8PointerCopies.Targets

theorem prefix_window (mode : Mode) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory)
    (observed count : Nat) (before : observed+count≤patchStart mode l) :
    ByteMemory.bytesAt (Listing8MainRetarget.finish mode l v state).principal.memory observed count=
      ByteMemory.bytesAt state.principal.memory observed count := by
  have coords:=coordinates mode l
  have input:=resources.inputAfter
  have source:=(Listing8LiteralInput.positions mode l.input).2.2.1
  apply Listing8MainRetarget.window mode l v resources reach state entry forward current observed count
  · right;dsimp [nodeParams,Listing8ModeOffsets.nodeEntry,patchLayout];omega
  · right;dsimp [transitionParams,Listing8ModeOffsets.transitionEntry,Listing8ModeOffsets.nodeEntry,patchLayout];omega
  · intro site member
    have bound:=Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member
    right
    change patchStart mode l+40≤site.owner ∧ _ at bound
    omega
  · right;omega

theorem initial (mode : Mode) (l : Layout) (v : Values mode) (resources : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    StringMacroTemplates.Intact mode (nodeParams mode l) (Listing8MainRetarget.finish mode l v state).principal.memory ∧
    StringMacroTemplates.Intact mode (transitionParams mode l) (Listing8MainRetarget.finish mode l v state).principal.memory := by
  have coords:=coordinates mode l
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  constructor
  · apply StringMacroTemplates.initial
    exact (prefix_window mode l v resources reach state entry forward current _ _ (coords.1.le.trans second)).trans
      (Listing8MainCopyImage.node_current mode l v _ current)
  · apply StringMacroTemplates.initial
    exact (prefix_window mode l v resources reach state entry forward current _ _ coords.2.1.le).trans
      (Listing8MainCopyImage.rule_current mode l v _ current)

theorem self_after (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (source copied : Nat) (value : Word mode)
    (member : Listing8OwnerSequence.Owner.pointer source copied value∈Listing8OwnerImage.owners mode l (values mode origin g node rule)) :
    patchStart mode l≤Listing8CopiedPointer.selfField mode source copied := by
  have originals:=Listing8GlobalMainBounds.originals mode origin l t g node rule ctx
  have main:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  have coords:=coordinates mode l
  simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h | h | h <;> cases h
  all_goals cases mode
  all_goals simp only [Listing8CopiedPointer.selfField,Listing8CopiedPointer.origin,pointerField,
    backEntry,forwardEntry,stateEntry,currentEntry,newEntry,directionEntry,nodeParams,transitionParams,patchLayout,
    Listing8ModeOffsets.nodeEntry,Listing8ModeOffsets.transitionEntry,pointerSpan,ReaderImage.totalSize,ReaderImage.labelOffset,
    reduceCtorEq,ite_true,ite_false]
  all_goals omega

theorem word_after (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (word : Word mode) (member : word∈[(values mode origin g node rule).back,(values mode origin g node rule).forward,
      (values mode origin g node rule).next,(values mode origin g node rule).newState]) : patchStart mode l≤word.toNat := by
  have main:=Listing8GlobalMainBounds.copy mode origin l t g node rule ctx
  have ordered:=Listing8GlobalControlLayout.ordered mode origin
  have coords:=coordinates mode l
  have late : StringWrites.WordOwned mode (Listing8FullTableImage.start mode origin)
      (Listing8GraphLayout.endPC mode origin g.transitions g.nodes) word := by
    simp only [values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Listing8LateGraphFieldBounds.node_word mode origin g (g.tape node).back ctx.native
    · exact Listing8LateGraphFieldBounds.node_word mode origin g (g.tape node).forward ctx.native
    · exact Listing8LateGraphFieldBounds.next_word mode origin g rule ctx.native
    · exact Listing8LateGraphFieldBounds.state_word mode origin g (g.rules rule).destination ctx.native
  have lower:=late.1
  omega

theorem placements (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ owner∈Listing8OwnerImage.owners mode l (values mode origin g node rule),
      Listing8OwnerStoreRegions.Placement mode (fun address _ => patchStart mode l≤address) owner := by
  intro owner member
  have coords:=coordinates mode l
  have before:=ctx.resources.inputAfter
  have input:=Listing8LiteralInput.positions mode l.input
  have direction:=Listing8DirectionLayout.positions mode (Listing8DirectionGeometry.region mode l)
  have located:=ctx.body.state.head.direction
  have ending:=input.2.2.2.2.2.2.2
  change Listing8LiteralInput.endPC mode l.input=_ at ending
  have directionAt:=direction.2.2.2.2.2.2.1
  change Listing8DirectionLayout.directionPC mode (Listing8DirectionGeometry.region mode l)=Listing8LiteralInput.endPC mode l.input+_ at directionAt
  simp only [Listing8OwnerImage.owners,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨self_after mode origin l t g node rule ctx _ _ (values mode origin g node rule).back (by simp [Listing8OwnerImage.owners]),word_after mode origin l t g node rule ctx _ (by simp)⟩
  · exact ⟨self_after mode origin l t g node rule ctx _ _ (values mode origin g node rule).forward (by simp [Listing8OwnerImage.owners]),word_after mode origin l t g node rule ctx _ (by simp)⟩
  · exact ⟨self_after mode origin l t g node rule ctx _ _ (values mode origin g node rule).next (by simp [Listing8OwnerImage.owners]),word_after mode origin l t g node rule ctx _ (by simp)⟩
  · change patchStart mode l≤Listing8LiteralInput.scalarField mode l.input
    rw [input.2.1];omega
  · change patchStart mode l≤Listing8LiteralInput.updateStart mode l.input+6
    rw [input.2.2.2.2.1];omega
  · change patchStart mode l≤l.direction+6
    rw [located,directionAt];cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at ending <;> omega
  · exact ⟨self_after mode origin l t g node rule ctx _ _ (values mode origin g node rule).newState (by simp [Listing8OwnerImage.owners]),word_after mode origin l t g node rule ctx _ (by simp)⟩

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringStoreRegions.Run mode (fun address _ => patchStart mode l≤address)
      ((Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map (StringStoreWrites.liftDword mode))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) :=
  Listing8OwnerStoreRegions.regions mode _ _ _ (Listing8CopiedOwners.chain mode l _)
    (Listing8CopiedOwners.valid mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx))
    (Listing8CopiedOwners.outside mode l _ ctx.resources (Listing8GraphInputContext.owners mode origin l t g node rule ctx))
    (placements mode origin l t g node rule ctx) _
    (Listing8MainRetarget.registers mode l _ ctx.resources ctx.fields.tapeReach state entry forward current).1
    (Listing8MainRetarget.owner_current mode l _ ctx.resources ctx.fields.tapeReach state entry forward current)

theorem all_decodes (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (current : Listing8MainCopyImage.Current mode l (values mode origin g node rule) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached =>
      StringEncodedTemplates.Decodes mode (nodeParams mode l) reached.principal.memory ∧
      StringEncodedTemplates.Decodes mode (transitionParams mode l) reached.principal.memory)
      ((Listing8OwnerSequence.program mode (Listing8OwnerImage.owners mode l (values mode origin g node rule))).map (StringStoreWrites.liftDword mode))
      (Listing8MainRetarget.finish mode l (values mode origin g node rule) state) := by
  have second:=endpoint_lower mode (secondStart mode l) (transitionSpan mode)
  change secondStart mode l≤patchStart mode l at second
  have property:=initial mode l _ ctx.resources ctx.fields.tapeReach state entry forward current
  have kept:=StringStoreTemplateRuns.preserve mode (fun address _ => patchStart mode l≤address)
    (fun memory => StringMacroTemplates.Intact mode (nodeParams mode l) memory ∧ StringMacroTemplates.Intact mode (transitionParams mode l) memory)
    _ _ property (fun memory address packet both after =>
      ⟨StringMacroTemplates.frame mode _ memory address packet both.1 (Or.inr (second.trans after)),
        StringMacroTemplates.frame mode _ memory address packet both.2 (Or.inr after)⟩)
    (regions mode origin l t g node rule ctx state entry forward current)
  exact StringTemplateStates.monotone mode _ _ _ _
    (fun reached both => ⟨StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.node.sizeFits both.1,
      StringEncodedTemplates.macro_decodes mode _ reached.principal.memory ctx.resources.transition.sizeFits both.2⟩) kept

end SmcTuring.Appendix.Listing8MacroOwnerFrames

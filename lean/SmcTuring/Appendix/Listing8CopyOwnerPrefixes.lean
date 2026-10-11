module
public import SmcTuring.Appendix.Listing8CopyTemplateWindows
public import SmcTuring.Appendix.Listing8MainCopies
public import SmcTuring.Appendix.Listing8NodeBlock
public import SmcTuring.Appendix.Listing8TransitionBlock

public section
namespace SmcTuring.Appendix.Listing8CopyOwnerPrefixes
open Native Listing8CopyImage Listing8Prototypes Listing8OwnerTemplateCollection

@[expose] def nodeTemplates (mode : Mode) (l : Layout) (v : Values mode) :=
  (Listing8NodeBlock.owners mode l.sourceNode ⟨v.tape,v.back,v.forward⟩).map (original mode)
@[expose] def transitionTemplates (mode : Mode) (l : Layout) (v : Values mode) :=
  (Listing8TransitionBlock.owners mode l.sourceTransition v).map (original mode)
@[expose] def Bounded (mode : Mode) (p : StringMacroLayout.Params) (templates : List (Template mode)) :=
  ∀ template∈templates,p.source≤start mode template ∧ start mode template+span mode template≤p.source+p.size

/-- Full setup followed by an arbitrary actual MOVS prefix. The exact copied
snapshot, byte count, original templates and completed copied headers are
all bound to this same reached state. -/
@[expose] def Certificate (mode : Mode) (p : StringMacroLayout.Params) (state : StringExecution.State mode)
    (templates : List (Template mode)) (before : List (StringStack.Form mode)) :=
  ∃ first rest : List Nat,StringPlan.widths mode p.size=first++rest ∧
    before=(StringMoves.forms mode first).map (StringWrites.liftString mode) ∧
    let current := StringWrites.run mode
      ((StringSetup.forms mode p.start p.source p.destination).map (StringWrites.liftString mode)++before) state
    current=StringMacroCopyPrefixes.reached mode p state first ∧
    current.principal.memory=ByteMemory.putBytes
      (StringFields.prepared mode (StringMacroLayout.layout mode p) state.principal.memory state.sourceIndex state.destinationIndex)
      p.destination (ByteMemory.bytesAt state.principal.memory p.source first.sum) ∧
    first.sum+rest.sum=p.size ∧ current.sourceIndex.toNat=p.source+first.sum ∧
    current.destinationIndex.toNat=p.destination+first.sum ∧ current.backwards=false ∧
    ∀ template∈templates,
      (Intact mode template current.principal.memory ∧ Decodes mode template current.principal.memory) ∧
      (start mode template-p.source+Listing8CopyTemplateWindows.header mode template≤first.sum →
        Intact mode (Listing8CopyTemplateWindows.relocate mode template (p.destination+(start mode template-p.source))) current.principal.memory ∧
        Decodes mode (Listing8CopyTemplateWindows.relocate mode template (p.destination+(start mode template-p.source))) current.principal.memory)

theorem constructed (mode : Mode) (p : StringMacroLayout.Params) (state : StringExecution.State mode)
    (ready : StringMacroLayout.Ready mode p state) (templates : List (Template mode))
    (intact : All mode templates state.principal.memory) (bounded : Bounded mode p templates)
    (before after : List (StringStack.Form mode))
    (cut : (StringMoves.forms mode (StringPlan.widths mode p.size)).map (StringWrites.liftString mode)=before++after) :
    Certificate mode p state templates before := by
  rcases StringCopyPrefixes.cut mode _ before after cut with ⟨first,rest,split,left,_⟩
  refine ⟨first,rest,split,left,?_⟩
  rw [left,StringMacroCopyPrefixes.whole_prefix]
  have bounds := StringMacroCopyPrefixes.prefix_bounds mode p state ready first rest split
  have indices := StringMacroCopyPrefixes.indices mode p state ready first rest split
  refine ⟨rfl,StringMacroCopyPrefixes.memory mode p state ready first rest split,bounds.2.2.2,
    indices.1,indices.2.1,indices.2.2,?_⟩
  intro template member
  have position := bounded template member
  have offset : start mode template=p.source+(start mode template-p.source) := by omega
  have within : start mode template-p.source+Listing8CopyTemplateWindows.header mode template≤p.size := by
    have head := (Listing8CopyTemplateWindows.header_bounds mode template).1
    omega
  refine ⟨Listing8CopyTemplateWindows.macro_source mode p state ready first rest split template
    (intact template member) _ offset within,?_⟩
  intro complete
  exact Listing8CopyTemplateWindows.macro_header mode p state ready first rest split template (intact template member) _ offset complete

theorem node_current (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory l.sourceNode (nodeSpan mode)=sourceNodeBytes mode l v) :
    All mode (nodeTemplates mode l v) memory :=
  original_current mode _ memory (Listing8NodeBlock.current mode l.sourceNode ⟨v.tape,v.back,v.forward⟩ memory current)

theorem transition_current (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l v) :
    All mode (transitionTemplates mode l v) memory :=
  original_current mode _ memory (Listing8TransitionBlock.current mode l.sourceTransition v memory current)

theorem node_bounded (mode : Mode) (l : Layout) (v : Values mode) :
    Bounded mode (nodeParams mode l) (nodeTemplates mode l v) := by
  intro template member
  rcases List.mem_map.mp member with ⟨owner,ownerMember,rfl⟩
  simp only [Listing8NodeBlock.owners,List.mem_cons,List.not_mem_nil,or_false] at ownerMember
  rcases ownerMember with rfl | rfl | rfl <;>
    simp only [original,start,span,nodeParams,backEntry,forwardEntry,nodeSpan] <;> omega

theorem transition_bounded (mode : Mode) (l : Layout) (v : Values mode) :
    Bounded mode (transitionParams mode l) (transitionTemplates mode l v) := by
  intro template member
  rcases List.mem_map.mp member with ⟨owner,ownerMember,rfl⟩
  simp only [Listing8TransitionBlock.owners,List.mem_cons,List.not_mem_nil,or_false] at ownerMember
  rcases ownerMember with rfl | rfl | rfl | rfl | rfl <;>
    simp only [original,start,span,transitionParams,currentEntry,newEntry,directionEntry,stateEntry,transitionSpan] <;> omega

theorem node_live (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory)
    (before after : List (StringStack.Form mode))
    (cut : (StringMoves.forms mode (StringPlan.widths mode (nodeParams mode l).size)).map (StringWrites.liftString mode)=before++after) :
    Certificate mode (nodeParams mode l) state (nodeTemplates mode l v) before :=
  constructed mode _ state (Listing8LiveCopies.first_ready mode l r state entry forward
    (Listing8MainCopyImage.node_current mode l v _ current)) _
    (node_current mode l v _ current.node) (node_bounded mode l v) before after cut

/-- The first actual full macro frames the second declaration's initial
source bytes. A later source image is positively derived. -/
theorem transition_source_after_first (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    ByteMemory.bytesAt (Listing8CopyTrace.first mode l state).principal.memory l.sourceTransition (transitionSpan mode)=
      sourceTransitionBytes mode l v := by
  have ready := Listing8LiveCopies.first_ready mode l r state entry forward (Listing8MainCopyImage.node_current mode l v _ current)
  rw [Listing8CopyTrace.first,StringMacroEffects.finish_effect mode _ _ ready]
  change ByteMemory.bytesAt (ByteMemory.putBytes state.principal.memory (nodeParams mode l).destination
    (ByteMemory.bytesAt state.principal.memory l.sourceNode (nodeSpan mode))) l.sourceTransition (transitionSpan mode)=_
  rw [byte_frame]
  · exact current.rule
  · simp only [ByteMemory.bytes_at_length]
    have positions := destinations mode l
    have afterInput := code_to_input mode l r
    rcases r.transitionOutside with early | late
    · right;omega
    · left;omega

theorem transition_live (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory)
    (before after : List (StringStack.Form mode))
    (cut : (StringMoves.forms mode (StringPlan.widths mode (transitionParams mode l).size)).map (StringWrites.liftString mode)=before++after) :
    Certificate mode (transitionParams mode l) (Listing8CopyTrace.first mode l state) (transitionTemplates mode l v) before := by
  have ready := Listing8LiveCopies.first_ready mode l r state entry forward (Listing8MainCopyImage.node_current mode l v _ current)
  have nextReady := Listing8LiveCopies.second_ready mode l r state ready (Listing8MainCopyImage.rule_current mode l v _ current)
  exact constructed mode _ _ nextReady _ (transition_current mode l v _ (transition_source_after_first mode l v r state entry forward current))
    (transition_bounded mode l v) before after cut

theorem transition_snapshot (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (ready : StringMacroLayout.Ready mode (nodeParams mode l) state)
    (source : ByteMemory.bytesAt state.principal.memory l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l v) :
    ByteMemory.bytesAt (Listing8CopyTrace.first mode l state).principal.memory l.sourceTransition (transitionSpan mode)=
      sourceTransitionBytes mode l v := by
  rw [Listing8CopyTrace.first,StringMacroEffects.finish_effect mode _ _ ready]
  change ByteMemory.bytesAt (ByteMemory.putBytes state.principal.memory (nodeParams mode l).destination
    (ByteMemory.bytesAt state.principal.memory l.sourceNode (nodeSpan mode))) l.sourceTransition (transitionSpan mode)=_
  rw [byte_frame]
  · exact source
  · simp only [ByteMemory.bytes_at_length]
    have positions := destinations mode l
    have afterInput := code_to_input mode l r
    rcases r.transitionOutside with early | late
    · right;omega
    · left;omega

@[expose] def Both (mode : Mode) (l : Layout) (v : Values mode) (state : StringExecution.State mode) :=
  (∀ before after : List (StringStack.Form mode),
    (StringMoves.forms mode (StringPlan.widths mode (nodeParams mode l).size)).map (StringWrites.liftString mode)=before++after →
    Certificate mode (nodeParams mode l) state (nodeTemplates mode l v) before) ∧
  (∀ before after : List (StringStack.Form mode),
    (StringMoves.forms mode (StringPlan.widths mode (transitionParams mode l).size)).map (StringWrites.liftString mode)=before++after →
    Certificate mode (transitionParams mode l) (Listing8CopyTrace.first mode l state) (transitionTemplates mode l v) before)

/-- Only present macro/source packets and static resources are needed. The
second macro, source image and all of its reached prefixes are constructed. -/
theorem pair (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false)
    (nodeMacro : ByteMemory.bytesAt state.principal.memory l.start (StringMacroLayout.bytes mode (nodeParams mode l)).length=
      StringMacroLayout.bytes mode (nodeParams mode l))
    (ruleMacro : ByteMemory.bytesAt state.principal.memory (secondStart mode l)
      (StringMacroLayout.bytes mode (transitionParams mode l)).length=StringMacroLayout.bytes mode (transitionParams mode l))
    (nodeSource : ByteMemory.bytesAt state.principal.memory l.sourceNode (nodeSpan mode)=sourceNodeBytes mode l v)
    (ruleSource : ByteMemory.bytesAt state.principal.memory l.sourceTransition (transitionSpan mode)=sourceTransitionBytes mode l v) :
    Both mode l v state := by
  have ready := Listing8LiveCopies.first_ready mode l r state entry forward nodeMacro
  have nextReady := Listing8LiveCopies.second_ready mode l r state ready ruleMacro
  refine ⟨?_,?_⟩
  · intro before after cut
    exact constructed mode _ state ready _ (node_current mode l v _ nodeSource) (node_bounded mode l v) before after cut
  · intro before after cut
    exact constructed mode _ _ nextReady _ (transition_current mode l v _ (transition_snapshot mode l v r state ready ruleSource))
      (transition_bounded mode l v) before after cut

end SmcTuring.Appendix.Listing8CopyOwnerPrefixes
